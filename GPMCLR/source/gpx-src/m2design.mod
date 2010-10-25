(****************************************************************)
(*								*)
(*		Modula-2 Compiler Source Module			*)
(*								*)
(*      Parser for Designators, and Designator Utilities        *)
(*								*)
(*    (c) copyright 1988 Faculty of Information Technology      *)
(*								*)
(*      original module : kjg 1-May-1988                        *)
(*      modifications   : new access mode code        04-Aug-88 *)
(*                      : InitDesignator  (JWH)       17-Oct-88 *)
(*			: cache uplevel high values   08-Mar-89 *)
(*			: SetAcc' now sets attr' bits 07-Mar-90 *)
(*								*)
(*   =============== merged mips and i386 source ============	*)
(*			   kjg 22 Mar 93			*)
(*                                                              *)
(****************************************************************
$Log: m2design.mod,v $
Revision 1.7  1997/01/16 02:36:32  gough
create code for preconNode-s
New procedure CloneDesig.  Better code for GetSelector

Revision 1.6  1996/01/08 05:26:31  gough
make use attributes of variables set types in m2nodedefs

# Revision 1.5  1995/03/23  22:54:42  gough
# SetAccessMode deals with multiple HIGH descriptors
#
# Revision 1.4  1995/02/23  03:48:21  lederman
# change CAST(BYTE,literal) to local fnc. to be ISO compliant
#
# Revision 1.3  1994/11/15  04:24:16  gough
# more accurate test IF (form >= openValForm ... with no conjunction
#
# Revision 1.2  1994/07/01  04:24:48  lederman
# parameterize bytesInBlock on host address size
#
# Revision 1.1  1994/04/07  04:48:31  lederman
# Initial revision
#
*****************************************************************)

IMPLEMENTATION MODULE M2Designators;
FROM SYSTEM IMPORT BYTE, TSIZE, CAST;
FROM M2NodeDefs IMPORT 
	VarUses, UsesSet,
	IdDesc, TypeDesc, TyNodeClass,
	Attribute, AttributeSet,
        FormalClass, IdTree, IdNodeClass, current;
FROM M2Alphabets IMPORT HashBucketType, SymbolSet,
        Flags, FlagSet, TerminalSymbols;
FROM GenSequenceSupport IMPORT Sequence;
FROM M2Scanner IMPORT lexAtt, symbol, GetSymbol, CurrentFlags;
FROM M2InOut IMPORT DiagName, Position, lastPos, Error, ErrIdent;
FROM M2NameHandler IMPORT anonBkt;
FROM M2TabInitialize IMPORT PointerTo;
FROM M2ExpParser IMPORT Expression, SkipTo;
FROM Storage IMPORT ALLOCATE;
FROM StdError IMPORT WriteString, WriteCard, WriteLn;
FROM ProgArgs IMPORT Assert;
(*
 *  not needed in native code versions
 *  FROM M2NamGenerate IMPORT MakeCacheName;
 *)

  CONST	bytesInBlock = adrSize + 2;

  TYPE	ExprClassSet = SET OF ExprNodeClass;

  TYPE	BlockPtr = POINTER TO Block;
	Block    = RECORD
                    next  : BlockPtr;
                    bytes : ARRAY [0 .. bytesInBlock - 1] OF BYTE;
                  END;

  PROCEDURE CAST_BYTE(par : BYTE) : BYTE; BEGIN RETURN par END CAST_BYTE;

(* ---------------------------------------------------- *)
  MODULE CacheManager;
  IMPORT CAST;
  IMPORT UsesSet, VarUses,
	 DesigRec, AccessMode, BlockPtr, Block, current,
	 AttributeSet, Attribute, IdNodeClass, Assert,
         IdDesc, FormalClass, BYTE, (* MakeCacheName, *)
         anonBkt, DiagName, WriteLn, WriteString, WriteCard;
  EXPORT SetAccessMode, ForceAccessMode, Summary, MaxCacheIndex;

    VAR dlc, ilc, uuc, duc, iuc, nextIndex : CARDINAL;


    PROCEDURE ForceAccessMode(VAR desig : DesigRec;
                                  mode  : AccessMode);
    BEGIN
      desig.firstSel^.bytes[0] := CAST(BYTE,mode);
      CASE mode OF
      | directLocl      : INC(dlc);
      | directNonL      : INC(duc);
      | indirect        : INC(ilc);
      | uplevel         : INC(uuc);
      | uplevelIndirect : INC(iuc);
      ELSE (* nothing for highAccess *)
      END;
    END ForceAccessMode;

    PROCEDURE SetAccessMode(VAR desig : DesigRec);
      VAR mode  : AccessMode; 
	  form  : FormalClass; 
	  local : BOOLEAN;
	  highD : IdDesc;
    (*
     *  here, current^ is the accessing scope,
     *  desig.variable^.decFrame is the target scope.
     *  If the target scope is a module then outside
     *  must be marked as containing uplevel objects.
     *)

      PROCEDURE MarkVarAndFrame(var : IdDesc);
	VAR stackFrame : IdDesc;
      BEGIN
	WITH var^ DO
	  INCL(varUseSet,uplevAcc);
	  (*
	   *  All frame objects after the first
	   *  are issued with cache names
	   *)
          stackFrame := decFrame;
	  IF stackFrame^.idClass = modNode THEN 
	    stackFrame := stackFrame^.outside;
	  END;
	  Assert(stackFrame^.body <> NIL);
 	  INCL(stackFrame^.body^.callAttrib,hasUplevObj);
	END;
      END MarkVarAndFrame;

    BEGIN (* assert : desig is a variable designator *)
      form := desig.variable^.varClass;
      local := desig.variable^.decFrame = current^.frame;
      IF local THEN (* direct, except for var and open *)
        IF form < varForm THEN mode := directLocl; INC(dlc);
        ELSE mode := indirect;                     INC(ilc);
        END;
      ELSIF (form >= static) AND (form <= extern) THEN 
	INCL(desig.variable^.varUseSet,uplevAcc);
        mode := directNonL; (* uplev but static *) INC(duc);
      ELSE (* auto or param *)
        IF NOT (uplevAcc IN desig.variable^.varUseSet) THEN
	  MarkVarAndFrame(desig.variable);
        END;
        IF form >= varForm THEN
          mode := uplevelIndirect; (* var, open *) INC(iuc);
	  IF (form >= openValForm) THEN
	  (*
           * (desig.variable^.nextHigh^.cshIndex = anonBkt) THEN
	   *  this is an uplevel access to an open array ==> it
	   *  is necessary to create a cache entry for the high
	   *  value, even if it is not explcitly accessed by a 
           *  HIGH() since it is needed for index bounds checks
	   *)
	    highD := desig.variable^.nextHigh;
	    REPEAT
	      INCL(highD^.varUseSet,uplevAcc);
	      highD := highD^.nextHigh;
	    UNTIL highD = NIL;
          END;
        ELSE mode := uplevel;      (* auto, val *) INC(uuc);
        END;
      END;
      desig.firstSel^.bytes[0] := CAST(BYTE,mode);
    END SetAccessMode;

    PROCEDURE MaxCacheIndex() : CARDINAL;
    BEGIN RETURN nextIndex END MaxCacheIndex;

    PROCEDURE Summary();
    BEGIN
(*
 *    WriteCard(dlc,6); WriteString(' direct accesses'); WriteLn;
 *    WriteCard(ilc,6); WriteString(' indirect accesses'); WriteLn;
 *    WriteCard(uuc,6); WriteString(' uplevel accesses'); WriteLn;
 *    WriteCard(duc,6); WriteString(' uplevel global accesses'); WriteLn;
 *    WriteCard(iuc,6); WriteString(' indirect uplevel accesses'); WriteLn;
 *    WriteCard(nextIndex-1,6);
 *    WriteString(' uplevel accessed objects'); WriteLn;
 *)
    END Summary;

  BEGIN
    nextIndex := 1;
    dlc := 0; ilc := 0; uuc := 0; duc := 0; iuc := 0;
  END CacheManager;
(* ---------------------------------------------------- *)

  PROCEDURE CreateExprDesc(VAR ptr : ExprDesc;
                               tag : ExprNodeClass);
    CONST tests = FlagSet{indexTests .. ovfloTests};
  BEGIN
    ALLOCATE(ptr,TSIZE(ExprRec));
    WITH ptr^ DO
      exprClass   := tag;
      actualClass := notActual;
      sourceLoc   := lastPos;
      testFlags   := CurrentFlags() * tests;
      IF tag IN ExprClassSet{andNode,orNode..notNode} THEN
        exprType := PointerTo(bools);
      ELSE exprType  := NIL;
      END;
      CASE tag OF
      | desigNode   : name.variable := NIL;
                      ALLOCATE(name.firstSel,TSIZE(Block)); 
		      name.firstSel^.next := NIL;
                      name.firstSel^.bytes[0] := CAST_BYTE(unresolved);
                      name.firstSel^.bytes[1] := CAST_BYTE(endMarker);
        (* others are formed by tag transformation *)
      | literalNode, repCountNode : (* nothing *)
      | preconNode  : evalLst := Sequence{NIL,NIL};
      ELSE leftOp := NIL; rightOp := NIL;
      END; (* case *)
    END;
  END CreateExprDesc;

(* ----------------------------------------------------- *)

  PROCEDURE CloneDesig(old : DesigRec; VAR new : DesigRec);
    VAR newB : BlockPtr;
	oldB : BlockPtr;
  BEGIN
    new.variable := old.variable;
    ALLOCATE(new.firstSel,TSIZE(Block));
    new.firstSel^ := old.firstSel^;
    oldB := old.firstSel;
    newB := new.firstSel;
    WHILE oldB^.next <> NIL DO
      ALLOCATE(newB^.next,TSIZE(Block));
      oldB := oldB^.next;
      newB := newB^.next;
      newB^ := oldB^;
    END;
   END CloneDesig;
    
(* ----------------------------------------------------- *)

(*
 * CONST max    = adrSize - 1;
 * TYPE  Secret = ARRAY[0 .. max] OF BYTE; (* this may violate ISO rules *)
 * ... it did, also GPM2 rules, so make it clear in the def file
 *)

  PROCEDURE InitDesignator(VAR desg : DesigRec);
  BEGIN
    desg.variable := NIL;
    ALLOCATE(desg.firstSel,TSIZE(Block)); desg.firstSel^.next := NIL;
    desg.firstSel^.bytes[0] := CAST_BYTE(unresolved);
    desg.firstSel^.bytes[1] := CAST_BYTE(endMarker);
  END InitDesignator;

  PROCEDURE InitDState(desig  : DesigRec;
                   VAR dState : DStateType);
  BEGIN
    dState.byte := 1;
    dState.curs := desig.firstSel;
  END InitDState;

  PROCEDURE SelectListBegin(desig : DesigRec;
                       VAR dState : DStateType);
  BEGIN
    dState.curs := desig.firstSel;
    dState.byte := 1;
  END SelectListBegin;

  PROCEDURE GetAnother(VAR dState : DStateType);
    VAR ptr : BlockPtr;
  BEGIN
    ALLOCATE(ptr,TSIZE(Block)); ptr^.next := NIL;
    dState.curs^.next := ptr;
    dState.curs := ptr;
    dState.byte := 0;
  END GetAnother;

  PROCEDURE PushSubscript(VAR dState : DStateType;
                              exp    : ExprDesc);
    VAR tricky : SelectAttribute; 
	index  : CARDINAL;
  BEGIN
    tricky.exp := exp;
    IF dState.byte >= bytesInBlock THEN GetAnother(dState) END;
    dState.curs^.bytes[dState.byte] := CAST_BYTE(subscriptNode);
    INC(dState.byte);
    FOR index := 0 TO adrSize - 1 DO
      IF dState.byte >= bytesInBlock THEN GetAnother(dState) END;
      dState.curs^.bytes[dState.byte] := tricky.bytes[index];
      INC(dState.byte);
    END;
  END PushSubscript;

  PROCEDURE PushIdentifier(VAR dState : DStateType;
                               fld    : HashBucketType);
    VAR tricky : SelectAttribute; ix : CARDINAL;
  BEGIN
    tricky.hsh := fld;
    IF dState.byte >= bytesInBlock THEN GetAnother(dState) END;
    dState.curs^.bytes[dState.byte] := CAST_BYTE(identifierNode);
    INC(dState.byte);
    FOR ix := 0 TO adrSize - 1 DO 
(* room for later transformation to IdDesc after binding *)
      IF dState.byte >= bytesInBlock THEN GetAnother(dState) END;
      dState.curs^.bytes[dState.byte] := tricky.bytes[ix];
      INC(dState.byte);
    END;
  END PushIdentifier;

  PROCEDURE PushDereference(VAR dState : DStateType);
  BEGIN
    IF dState.byte >= bytesInBlock THEN GetAnother(dState) END;
    dState.curs^.bytes[dState.byte] := CAST_BYTE(dereferenceNode);
    INC(dState.byte);
  END PushDereference;

  PROCEDURE SelectListEnd(dState : DStateType);
  BEGIN
    IF dState.byte < bytesInBlock THEN
      dState.curs^.bytes[dState.byte] := CAST_BYTE(endMarker);
    END; (* and in any case *)
    dState.curs^.next := NIL;
  END SelectListEnd;

  PROCEDURE MoveSelectors(VAR desig : DesigRec;
                              dStat : DStateType);
    VAR start : DStateType;
  BEGIN (* assert: final select list is shorter than original *)
    start.curs := desig.firstSel;
    start.byte := 1;
    IF dStat.byte = bytesInBlock THEN
      dStat.curs := dStat.curs^.next; dStat.byte := 0;
    END;
    WHILE dStat.curs <> NIL DO
      start.curs^.bytes[start.byte] := dStat.curs^.bytes[dStat.byte];
      IF start.byte = bytesInBlock - 1 THEN
        start.curs := start.curs^.next; start.byte := 0;
      ELSE INC(start.byte);
      END;
      IF dStat.byte = bytesInBlock - 1 THEN
        dStat.curs := dStat.curs^.next; dStat.byte := 0;
      ELSE INC(dStat.byte);
      END;
    END;
    start.curs^.bytes[start.byte] := CAST_BYTE(endMarker);
  END MoveSelectors;

  PROCEDURE AccessModeOf(desig : DesigRec) : AccessMode;
  BEGIN
    RETURN CAST(AccessMode,desig.firstSel^.bytes[0]);
  END AccessModeOf;

  PROCEDURE EmptySelList(desig : DesigRec) : BOOLEAN;
  BEGIN
    RETURN (desig.firstSel = NIL) OR 
           (desig.firstSel^.bytes[1] = CAST_BYTE(endMarker));
  END EmptySelList;

  PROCEDURE GetSelector(VAR dState : DStateType;
                        VAR selVal : SelectAttribute);
    VAR tricky : SelectAttribute; ix : CARDINAL;
  BEGIN (* dState.byte is the next node to read *)
    IF dState.byte >= bytesInBlock THEN
      dState.curs := dState.curs^.next;
      dState.byte := 0;
    END;
    IF dState.curs = NIL THEN selVal.tag := endMarker;
    ELSE
      selVal.tag := CAST(SelectNodeClass,dState.curs^.bytes[dState.byte]);
      INC(dState.byte);
      IF selVal.tag >= subscriptNode THEN
        FOR ix := 0 TO adrSize - 1 DO
          IF dState.byte >= bytesInBlock THEN
            dState.curs := dState.curs^.next;
            dState.byte := 0;
          END;
          tricky.bytes[ix] := dState.curs^.bytes[dState.byte];
          INC(dState.byte);
        END;
      END;
      CASE selVal.tag OF
      | subscriptNode    : selVal.exp := tricky.exp;
      | fieldExtractNode : selVal.fid := tricky.fid;
      | identifierNode   : selVal.hsh := tricky.hsh;
      ELSE (* nothing *)
      END;
    END;
  END GetSelector;

  PROCEDURE BindFieldName(desg   : DesigRec;
                      VAR dState : DStateType;
                          fldPtr : IdDesc);
    VAR tricky : SelectAttribute;
        ptr : BlockPtr;
        ix : CARDINAL;
  BEGIN
    IF dState.byte >= adrSize + 1 THEN (* n = 5 or 6 *)
      DEC(dState.byte,adrSize + 1);
    ELSE (* n <= 4, the hard one, must back up cursor *)
      ptr := desg.firstSel;
      WHILE ptr^.next <> dState.curs DO ptr := ptr^.next END;
      dState.curs := ptr; INC(dState.byte,(bytesInBlock - adrSize - 1));
    END;
    tricky.fid := fldPtr;
    dState.curs^.bytes[dState.byte] := CAST_BYTE(fieldExtractNode);
    INC(dState.byte);
    FOR ix := 0 TO adrSize - 1 DO
      IF dState.byte >= bytesInBlock THEN
        dState.curs := dState.curs^.next;
        dState.byte := 0;
      END;
      dState.curs^.bytes[dState.byte] := tricky.bytes[ix];
      INC(dState.byte);
    END;
  END BindFieldName;

(* ----------------------------------------------------- *)

  PROCEDURE ParseDesignator(halt : SymbolSet;
                        VAR desg : DesigRec);
    VAR new : SymbolSet;
        exp : ExprDesc;
        hsh : HashBucketType;
        state : DStateType;
  BEGIN (* assert: symbol = ident *)
    new := halt; INCL(new,rBrac); INCL(new,comma);
    hsh := lexAtt.hashIx;
    SelectListBegin(desg,state);
    PushIdentifier(state,hsh);
    GetSymbol; (* read past ident *)
    LOOP
      CASE symbol OF
      | upArrow :
          PushDereference(state); GetSymbol;
      | dot :
          GetSymbol;
          IF symbol <> ident THEN Error(108);
          ELSE
            hsh := lexAtt.hashIx;
            PushIdentifier(state,hsh);
            GetSymbol; (* ident *)
          END;
      | lBrac :
          GetSymbol;
          Expression(new,exp);
          PushSubscript(state,exp);
          WHILE symbol = comma DO
            GetSymbol;
            Expression(new,exp);
            PushSubscript(state,exp);
          END;
          IF symbol = rBrac THEN GetSymbol;
          ELSE Error(115);
          END;
      ELSE EXIT;
      END (* case *)
    END; (* loop *)
    SelectListEnd(state);
(*
 *  SkipTo(halt,125);
 *)
  END ParseDesignator;

END M2Designators.

