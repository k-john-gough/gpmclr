(****************************************************************)
(*                                                              *)
(*             Modula-2 Compiler Source Module                  *)
(*                                                              *)
(*                 Static Semantic Utilities                    *)
(*                                                              *)
(*           (c) copyright 1987 SoftWare Automata.              *)
(*                                                              *)
(*      original module : from M2Parser kjg july 1987           *)
(*      modifications   :                                       *)
(*                      : 12-Jun-88, computing access modes     *)
(*                      : 10-Aug-88 jrh Compatibility checks    *)
(*                      : 24-Aug-88 jrh Compatibility checks    *)
(*                      : 25-Aug-88 jrh OpenCompatible result   *)
(*                      : 02-Sep-88 kjg Extend IsOrd. to ZZ etc *)
(*                      : 14-Sep-88 jrh Proc comp to Compatible *)
(*                      : 17-Feb-89 jrh Index and range checks  *)
(*      		: 24-Feb-89 jrh Subranges assign compat *)
(*			: 09-Mar-89 kjg resolvedType compat     *)
(*			: 16-Mar-89 jrh CheckedAssignCompat     *)
(*			: 24-Mar-89 kjg CheckValidAllocate	*)
(*			: 26-Mar-89 kjg new proc TypesOverlap?  *)
(*			: 18-Apr-89 kjg remove proc FindAccess  *)
(*			: 24-May-89 jrh size and alignment      *)
(*			: 26-May-89 jrh word alignment required *)
(*			: 7,10-Jun-89 kjg HasComplexActuals	*)
(*			: 16-Aug-89 kjg FixTypeAndValue (new)   *)
(*			: 16-Oct-89 kjg fix of FixType...	*)
(*			:  8-Nov-89 kjg BindFieldOffsets	*)
(*			: 13-Jun-90 kjg handling lexLevel	*)
(*			: 20-Jul-90 kjg new ConstAssignCompat.  *)
(*			: 25-Jul-90 kjg/ar fix of 2'nd 318 diag *)
(*			:  8-Sep-90 kjg uses M2Machin alignMap  *)
(*			:    Feb-92 kjg LookupAndMarkLevel loop *)
(*			: 03-Mar-92 jrh import TypeRec		*)
(*			: 09-Mar-92 kjg EquivTypes for result	*)
(*			: 14-May-92 jrh EquivFormals VAR/value	*)
(*                                                              *)
(****************************************************************
$Log: m2ssutil.mod,v $
Revision 1.15  1997/01/16 05:07:57  gough
        New code for precondition handling, including new test for
        equivalent procedure types.

Revision 1.14  1996/11/27 02:54:04  lederman
set up the codeBlkList and nestBlk STRINGs

Revision 1.13  1996/08/28 23:03:30  gough
remove alignment check in VarOpenComp. when dealing with stringTs.
The allocated block is always maximally aligned

Revision 1.12  1996/08/06 23:43:41  gough
fix up comment on multi-dimensional arrays

Revision 1.11  1996/07/30 00:02:40  gough
treat stringTs properly

Revision 1.10  1996/03/06 05:57:17  lederman
fix the retCut test in Compatible() yet again

Revision 1.9  1996/02/06 23:38:02  lederman
fix test for funcType to match procType in Compatible()

Revision 1.8  1995/11/20 02:30:02  gough
fix up evaluation of is_big_set predicate in HasCalls
second factor is "... AND size > bytesInWord"

Revision 1.7  1995/10/25 01:12:28  lederman
UU are compatible with hugeInt

Revision 1.6  1995/10/10 23:53:31  lederman
replace ExprCost() & HasComplexActuals() with HasCalls()

# Revision 1.5  1995/03/23  23:08:03  gough
# Va*OpenCompatible now takes extra parameter
#
# Revision 1.4  1995/03/14  01:51:58  gough
# Split OpenCompatible into two, new local procedure AssignCompatible
#
# Revision 1.3  1995/03/02  08:55:24  gough
# case for castNode node type
#
# Revision 1.2  1994/04/26  23:20:16  lederman
# protect IndexCardinality() against nil ty^.indexType
#
# Revision 1.1  1994/04/07  05:21:46  lederman
# Initial revision
#
*****************************************************************)

IMPLEMENTATION MODULE M2SSUtilities;

IMPORT M2TabInitialize, StdError;
FROM SYSTEM IMPORT CAST;
FROM M2NodeDefs  IMPORT 
        IdDesc, IdTree, IdNodeClass, IdClassSet, 
	IdString, codeBlkList,
        TypeRec, TypeDesc, TyNodeClass, TyClassSet,
        FormalType, FormalClass, FormalRec, modState, 
        thisCompileUnit, current, lexLevel, globalModList;

FROM M2Designators IMPORT 
	AccessMode, ExprNodeClass, ExprDesc, ExprRec,
	ActualParMode, DesigRec, DStateType, SelectAttribute,
	SelectNodeClass, InitDState, GetSelector, EmptySelList;

FROM M2InOut IMPORT lastPos, Position, Error, ErrIdent, DiagName;

FROM M2Alphabets IMPORT 
	LexAttType, HashBucketType, ModStateFlags, ModStateSet, Flags;

FROM M2MachineConstants IMPORT 
	bytesInWord, bytesInReal, alignMap, 
	intMax, charMax, cardMax, wordSize, byteSize; 

FROM GenSequenceSupport IMPORT Sequence, ElemPtr, Ended, 
                        LinkRight, InitCursor, GetNext;

FROM M2TabInitialize IMPORT PointerTo;
FROM M2StructureDefs IMPORT RangeDesc;
FROM M2NameHandler IMPORT anonBkt, MarkUsed, GetSourceRep;
FROM ProgArgs IMPORT Assert;

FROM StdError IMPORT Write, WriteString, WriteCard, WriteLn;

FROM VARSTRS IMPORT APPEND;
FROM Storage IMPORT ALLOCATE, DEALLOCATE;

(*$S-*) (*$I-*) (*$R-*)

    TYPE ExprClassSet = SET OF ExprNodeClass;

(******************************************************)

    TYPE ErrorRec  = RECORD
			leftT, rightT : TypeDesc;
		     END;

    TYPE ErrorPair = POINTER TO ErrorRec;

    VAR globalLeft, globalRight : TypeDesc;

    PROCEDURE QualTypeName(type : TypeDesc);
    BEGIN
      IF type = NIL THEN WriteString("invalid type");
      ELSE
	Write("<");
        DiagName(type^.parentMod^.name);
        Write(".");
        IF type^.tyName <> anonBkt THEN 
	  DiagName(type^.tyName);
        ELSE 
	  WriteString("$Anon"); 
	  WriteCard(CAST(CARDINAL,type) DIV 4 MOD 100, 0);
        END;
	Write(">");
	IF type^.tyClass = subranges THEN
	  WriteString(" (subrange of ");
	  QualTypeName(type^.hostType);
	  Write(")");
	END;
      END;
    END QualTypeName;

(*
    (*
     *   This procedure sets up a dummy error entry with the same line
     *   but with a position which is the cast value of the type
     *   pair record for the failed test. The pair of types are picked
     *   up from the global positions where they are placed by the
     *   other procedures of this module.
     *
     *   These records are recognizable by the error number of 0
     *)

    PROCEDURE SaveTypeErrorInfo();
      VAR pair : ErrorPair;
	  save : CARDINAL;
    BEGIN
      NEW(pair);
      WITH pair DO
	leftT := globalLeft;
	rightT := globalRight;
      END;
      save := lastPos.pos;
      lastPos.pos := CAST(CARDINAL,pair);
      Error(0);
      lastPos.pos := save;
    END SaveTypeErrorInfo;
*)

    PROCEDURE LoadGlobals(l, r : TypeDesc);
    BEGIN
      globalLeft := l;
      globalRight := r;
    END LoadGlobals;

    PROCEDURE DisplayLeftType();
    BEGIN
      QualTypeName(globalLeft);
    END DisplayLeftType;

    PROCEDURE DisplayRightType();
    BEGIN
      QualTypeName(globalRight);
    END DisplayRightType;
   
(****************************************************)
(*               Utility Procedures                 *)
(****************************************************)

              (* scope handling procedures *)

    PROCEDURE LookupInThisScope(tree : IdTree;
                                hsIx : HashBucketType;
                            VAR desc : IdDesc);
    BEGIN
      WHILE tree <> NIL DO
        WITH tree^ DO
          IF hsIx < name THEN tree := left;
          ELSIF hsIx > name THEN tree := right;
          ELSE desc := ident; RETURN;
          END;
        END; (* with *)
      END; (* normal exit ==> not found *)
      desc := NIL;
    END LookupInThisScope;      

    PROCEDURE LookupAndMarkUplevel( key   : HashBucketType;
				VAR found : IdDesc); (* NIL if not found *)
      VAR block : IdDesc;
    BEGIN
      block := current;
      LookupInThisScope(block^.scope, key, found);
      IF found = NIL THEN (* non local *)
        block := block^.uphill;
        WHILE (found = NIL) AND (block <> NIL) DO
	  LookupInThisScope(block^.scope, key, found);
	  block := block^.uphill;
        END;
	IF found <> NIL THEN MarkUsed(current^.body^.usedBkts, key) END;
      END;
    END LookupAndMarkUplevel;

    PROCEDURE Lookup(key   : HashBucketType;
                 VAR found : IdDesc); (* NIL if not found *)
      VAR block : IdDesc;
    BEGIN
      block := current;
      REPEAT
        LookupInThisScope(block^.scope, key, found);
        block := block^.uphill;
      UNTIL (found <> NIL) OR (block = NIL);
    END Lookup;

    PROCEDURE LookupInModList(hsh : HashBucketType;
                              VAR ptr : IdDesc);
       VAR curs  : ElemPtr;
           found : BOOLEAN;
    BEGIN
      InitCursor(globalModList,curs);
      found := FALSE;
      WHILE NOT found AND NOT Ended(curs) DO
        GetNext(curs,ptr);
        found := ptr^.name = hsh;
      END;
      IF NOT found THEN ptr := NIL END;
    END LookupInModList;

(* ============================================= *
 *  PROCEDURE DiagString(str : IdString);
 *    VAR ix : INTEGER;
 *  BEGIN
 *    DiagName(current^.name); Write(":");
 *    FOR ix := 0 TO HIGH(str) DO
 *	DiagName(str[ix]^.name);
 *	IF str[ix]^.idClass = modNode THEN
 *	  WriteString("(M),");
 *	ELSE
 *	  WriteString("(P),");
 *	END;
 *    END;
 *    WriteLn;
 *  END DiagString;
 * ============================================= *)

    MODULE CurrentScopeHandler;
    IMPORT APPEND, ALLOCATE, DEALLOCATE, codeBlkList;
IMPORT StdError, DiagName, IdString;
    IMPORT IdDesc, IdNodeClass, Error, current, lexLevel;
    EXPORT EnterScope, ExitScope, SetCurrentScope;

    VAR thisIdDesc : IdDesc;

    PROCEDURE SetCurrentScope(id : IdDesc);
    BEGIN current := id END SetCurrentScope;

    PROCEDURE EnterScope(id : IdDesc);
    BEGIN
      IF id^.idClass = modNode THEN
        id^.outside := thisIdDesc;
      ELSE (* class is proc or func *)
        id^.uphill  := thisIdDesc;
	INC(lexLevel);
	IF lexLevel = 18 THEN Error(320); lexLevel := 0 END;
      END;

     (*
      *  The nestBlk lists are in order of textual occurrence.
      *  The global codeBlkList string has the blocks in bottom-up 
      *  left-to-right order corresponding to a preorder treewalk.
      *)
      IF (thisIdDesc <> NIL) AND
	 (id^.idClass <> unknown) THEN 
	APPEND(thisIdDesc^.body^.nestBlks, id);
(*
   StdError.WriteString("Appending ");
   DiagName(id^.name);
   StdError.WriteString(" on nestBlk of ");
   DiagName(thisIdDesc^.name);
   StdError.WriteString(" length now ");
   StdError.WriteCard(HIGH(thisIdDesc^.body^.nestBlks)+1,0);
   StdError.WriteLn;
 *)
      END;

      thisIdDesc := id;
      current := id;
    END EnterScope;

    PROCEDURE ExitScope;
      VAR id : IdDesc;
    BEGIN
      id := thisIdDesc;
      IF id^.idClass = modNode THEN
        thisIdDesc := id^.outside;
      ELSE (* class is proc, func, or "unknown" *)
        thisIdDesc := id^.uphill;
	DEC(lexLevel);
      END;
      current := thisIdDesc;
      IF (thisIdDesc <> NIL) AND
	 (id^.idClass <> unknown) THEN
	APPEND(codeBlkList, id);
      END;
    END ExitScope;

    BEGIN
      thisIdDesc := NIL;
    END CurrentScopeHandler;

    (****************************************************)

    PROCEDURE OrdinalValue(t1 : TypeDesc;
                           v1 : LexAttType) : CARDINAL;
    BEGIN
      IF t1 <> NIL THEN
        CASE t1^.tyClass OF
          cards, ints, bools, enums, UU, ZZ, II : RETURN v1.fixValue;
        | chars, S1 : RETURN ORD(v1.charValue);
        | subranges : RETURN OrdinalValue(t1^.hostType,v1);
        ELSE Error(206); RETURN 0;
        END;
      ELSE RETURN 0;
      END;
    END OrdinalValue;

    PROCEDURE MinOfOrdType(ty : TypeDesc) : CARDINAL;
    BEGIN
      IF ty = NIL THEN RETURN 0 END;
      CASE ty^.tyClass OF
      | subranges : RETURN ty^.minRange;
      | ints,II,UU: RETURN intMax + 1; (* !!! *)
      | enums, chars, bools, cards, ZZ, S1 : RETURN 0;
      ELSE Error(206); RETURN 0;
      END;
    END MinOfOrdType;

    PROCEDURE MaxOfOrdType(ty : TypeDesc) : CARDINAL;
    BEGIN
      IF ty = NIL THEN RETURN 0 END;
      CASE ty^.tyClass OF
        subranges : RETURN ty^.maxRange;
      | enums     : RETURN ty^.cardinality - 1;
      | chars, S1 : RETURN charMax;
      | bools     : RETURN 1;
      | ints, ZZ  : RETURN intMax;
      | cards,UU,II : RETURN cardMax; (* assumes 2's complement! *)
      ELSE Error(206); RETURN 0;
      END;
    END MaxOfOrdType;

    PROCEDURE IndexCardinality(ty : TypeDesc) : CARDINAL;
    BEGIN
      Assert(ty^.tyClass = arrays);
      IF ty^.indexType = NIL THEN RETURN 0 END;
      WITH ty^.indexType^ DO
        CASE tyClass OF
          chars : RETURN charMax + 1;
        | cards : RETURN 0; (* cardMax + 1 *)
        | bools : RETURN 2;
        | enums : RETURN cardinality;
        | subranges : RETURN CAST(INTEGER,maxRange) - 
				CAST(INTEGER,minRange) + 1;
        END;
      END;
    END IndexCardinality;

    PROCEDURE Compatible(t1, t2 : TypeDesc) : BOOLEAN;
      VAR tc1, tc2 : TyNodeClass; tmp : TypeDesc;

      PROCEDURE EquivFormals (p1, p2 : Sequence (* of formal types *) ) : 
                                                                 BOOLEAN; 
      (*
       *   Return TRUE iff p1 & p2 match in number, form, and type.
       *)

      VAR
        p1Curs, p2Curs : ElemPtr;
        p1Formal, p2Formal : FormalType;

      BEGIN
        InitCursor (p1, p1Curs);
        InitCursor (p2, p2Curs);
        WHILE NOT Ended(p1Curs) AND NOT Ended(p2Curs) DO
          GetNext (p1Curs, p1Formal);
          GetNext (p2Curs, p2Formal);
	  IF (p1Formal^.form # p2Formal^.form) OR
	     NOT EquivTypes (p1Formal^.type, p2Formal^.type) THEN
	    RETURN FALSE;
	  END;
        END;
        RETURN(Ended(p1Curs) AND Ended(p2Curs))
      END EquivFormals;

      PROCEDURE EquivTypes(t1,t2 : TypeDesc) : BOOLEAN;
      BEGIN
        IF (t1 <> t2) THEN (* one last chance *)
          IF (t1 = NIL) OR
             (t2 = NIL) THEN RETURN FALSE;
          ELSE
            IF t1^.tyClass = opaqueTemp THEN
              t1 := t1^.resolvedType END;
            IF t2^.tyClass = opaqueTemp THEN
              t2 := t2^.resolvedType END;
          END;
        END;
	RETURN t1 = t2;
      END EquivTypes;


      PROCEDURE HasOpenArrays(seq : Sequence) : BOOLEAN;
        VAR pCurs : ElemPtr;
	    pElem : FormalType;
      BEGIN
	InitCursor (seq,pCurs);
	WHILE NOT Ended(pCurs) DO
	  GetNext(pCurs,pElem);
	  IF pElem^.form >= openValForm THEN RETURN TRUE END;
	END;
	RETURN FALSE;
      END HasOpenArrays;

    BEGIN (* NIL is compatible with everything ! *)
      globalLeft := t1;
      globalRight := t2;
      LOOP 
       (*
        *  this code successively changes the types so that
        *  a simple test may finally be applied. subranges are
        *  changed to their host types, and opaqueTemps to 
        *  their resolved types. If necessary params are swapped
        *  so that these transformations are applied to the 
        *  appropriate param. These transformations depend on
        *  subranges having the greatest class ord, and opaques
        *  having a greater ord than pointers
        *)
        IF (t1 = t2) OR (t1 = NIL) OR (t2 = NIL) THEN RETURN TRUE END;
        tc1 := t1^.tyClass; 
        tc2 := t2^.tyClass;
        IF tc2 = subranges THEN t2 := t2^.hostType;
        ELSIF tc2 = opaqueTemp THEN t2 := t2^.resolvedType; (* 9-Mar *)
        ELSIF tc1 > tc2 THEN tmp := t1; t1 := t2; t2 := tmp;
        ELSE
          CASE tc1 OF (* remember tc1 <= tc2 *)
            II : RETURN (tc2 IN TyClassSet{ZZ,ints,hInts})
          | ZZ : RETURN (tc2 IN TyClassSet{UU,cards,ints,hInts})
          | UU : RETURN (tc2 IN TyClassSet{cards,hInts})
          | RR : RETURN (tc2 = floats) OR (tc2 = doubles)
          | chars : RETURN (tc2 = S1)
          | adrs : RETURN (tc2 IN 
			TyClassSet{hiddens,opaqueTemp,pointers,stringTs})
	  | S1,SS : RETURN (tc2 = S1) OR (tc2 = SS);		(* Oct 92 *)

          (* Procedures are compatible if structurally equivalent *)
          | procTypes : 
		(* special check for direct to C procedures *)
		IF ((t1^.parentMod = thisCompileUnit) OR
		    NOT t1^.parentMod^.direct )   <> 
	           ((t2^.parentMod = thisCompileUnit) OR
		    NOT t2^.parentMod^.direct ) THEN
		  IF HasOpenArrays(t1^.params) THEN Error(318) END;
		END;
		IF (((t1^.parentMod = thisCompileUnit)    AND
			        (retCutAll IN modState)   OR 
		    (t1^.parentMod^.idClass = exportNode) AND
				 t1^.parentMod^.retCut))  <>
		   (((t2^.parentMod = thisCompileUnit)    AND
				(retCutAll IN modState)   OR 
		    (t2^.parentMod^.idClass = exportNode) AND
				t2^.parentMod^.retCut)) THEN
		  Error(318);	(* should be a new number *)
	        END;
		RETURN ((tc2 = procTypes) AND
                        EquivFormals (t1^.params, t2^.params) AND
			EquivPrecons (t1^.preCon, t2^.preCon));
          | funcTypes : 
		(* special check for direct to C procedures *)
		IF ((t1^.parentMod = thisCompileUnit) OR
		    NOT t1^.parentMod^.direct )   <> 
	           ((t2^.parentMod = thisCompileUnit) OR
		    NOT t2^.parentMod^.direct ) THEN
		  IF HasOpenArrays(t1^.params) THEN Error(318) END;
		END;
		IF (((t1^.parentMod = thisCompileUnit)    AND
			        (retCutAll IN modState)   OR 
		    (t1^.parentMod^.idClass = exportNode) AND
				 t1^.parentMod^.retCut))  <>
		   (((t2^.parentMod = thisCompileUnit)    AND
				(retCutAll IN modState)   OR 
		    (t2^.parentMod^.idClass = exportNode) AND
				t2^.parentMod^.retCut)) THEN
		  Error(318);	(* should be a new number *)
	        END;
		RETURN ((tc2 = funcTypes) AND
                        EquivFormals (t1^.params, t2^.params) AND
			EquivTypes   (t1^.result, t2^.result) AND
			EquivPrecons (t1^.preCon,t2^.preCon));
          ELSE RETURN FALSE
          END; (* case *)
        END; (* if *)
      END; (* loop *)
    END Compatible;

    PROCEDURE EquivPrecons(l,r : ExprDesc) : BOOLEAN;

      PROCEDURE ExprEq(e1,e2 : ExprDesc) : BOOLEAN;
	VAR class : ExprNodeClass;
	    ix    : CARDINAL;

	PROCEDURE DesigEq(d1,d2 : DesigRec) : BOOLEAN;
	  VAR v1,v2 : IdDesc;
	      s1,s2 : DStateType;
	      a1,a2 : SelectAttribute;
	BEGIN
	 (* check the entire variable part *)
	  v1 := d1.variable; v2 := d2.variable;
	  IF v1^.idClass <> v2^.idClass THEN RETURN FALSE;
	  ELSIF v1^.idClass = posParNode THEN
	    IF v1^.posIndex <> v2^.posIndex THEN RETURN FALSE END;
	  ELSE
	    IF v1 <> v2 THEN RETURN FALSE END;
	  END;
	 (* check the selectors, if any *)
	  InitDState(d1,s1);
	  InitDState(d2,s2);
	  LOOP
	    GetSelector(s1,a1);
	    GetSelector(s2,a2);
	    IF a1.tag <> a2.tag THEN RETURN FALSE END;
	    CASE a1.tag OF
	    | dereferenceNode : (* skip *)
	    | endMarker : RETURN TRUE;
	    | subscriptNode : 
		IF NOT ExprEq(a1.exp,a2.exp) THEN RETURN FALSE END;
	    | fieldExtractNode :
		IF a1.fid <> a2.fid THEN RETURN FALSE END;
	    END;
	  END;
	END DesigEq;

	PROCEDURE ParamsEq(d1,d2 : Sequence) : BOOLEAN;
	  VAR c1,c2 : ElemPtr;
	      e1,e2 : ExprDesc;
	BEGIN
	  InitCursor(d1,c1);
	  InitCursor(d2,c2);
	  WHILE NOT Ended(c1) AND NOT Ended(c2) DO
	    GetNext(c1,e1);
	    GetNext(c2,e2);
	    IF NOT ExprEq(e1,e2) THEN RETURN FALSE END;
	  END;
	  RETURN Ended(c1) AND Ended(c2);  (* _both_ must be ended *)
	END ParamsEq;

        PROCEDURE ConstructEq(d1,d2 : Sequence) : BOOLEAN;
	  VAR c1,c2 : ElemPtr;
	      e1,e2 : RangeDesc;
	BEGIN
	  InitCursor(d1,c1);
	  InitCursor(d2,c2);
	  WHILE NOT Ended(c1) AND NOT Ended(c2) DO
	    GetNext(c1,e1);
	    GetNext(c2,e2);
	    IF NOT ExprEq(e1^.lower,e2^.lower) THEN RETURN FALSE END;
	    IF e1^.upper <> NIL THEN
	      IF (e2^.upper = NIL) OR
		 NOT ExprEq(e1^.upper,e2^.upper) THEN RETURN FALSE END;
	    ELSIF e2^.upper <> NIL THEN RETURN FALSE;
	    END;
	  END;
	  RETURN Ended(c1) AND Ended(c2);  (* _both_ must be ended *)
	END ConstructEq;

      BEGIN (* ExprEq *)
	IF (e1^.exprClass <> e2^.exprClass) OR  
	   NOT Compatible(e1^.exprType,e2^.exprType) THEN RETURN FALSE;
	ELSE
	  class := e1^.exprClass;
	  CASE class OF
	  | desigNode :
	      RETURN DesigEq(e1^.name,e2^.name);
	  | funcDesigNode :
	      RETURN DesigEq(e1^.name,e2^.name) AND
		     ParamsEq(e1^.paramSeq,e2^.paramSeq);
	  | constructorNode, setDesigNode :
	      RETURN ConstructEq(e1^.rangeSeq,e2^.rangeSeq);
	  | literalNode :
	      FOR ix := 0 TO bytesInReal DO
		IF e1^.conValue.bytes[ix] <> 
		   e2^.conValue.bytes[ix] THEN RETURN FALSE END;
	      END;
	      RETURN TRUE;
	  | notNode, negateNode :
	      RETURN ExprEq(e1^.leftOp,e2^.leftOp);
	  ELSE (* binops *)
	      RETURN (class <= inNode) AND
		     ExprEq(e1^.leftOp,e2^.leftOp) AND
		     ExprEq(e1^.rightOp,e2^.rightOp);
	  END;
	END;
      END ExprEq;

    BEGIN (* EquivPrecons *)
      IF r = NIL THEN RETURN TRUE;		(* no condition on right ok *)
      ELSIF l = NIL THEN RETURN FALSE;	(* if rhs, then lhs needed  *)
      ELSE RETURN ExprEq(l,r);		(* otherwise test equiv'nce *)
      END;
    END EquivPrecons;

    PROCEDURE IsSignedType(ty : TypeDesc) : BOOLEAN;
    BEGIN
      IF ty = NIL THEN RETURN FALSE;
      ELSE RETURN (ty^.tyClass IN TyClassSet{ints,II,hInts}) OR
         ((ty^.tyClass = subranges) AND IsSignedType(ty^.hostType));
      END;
    END IsSignedType;

    PROCEDURE FixTypeAndValue(VAR v : LexAttType;
			      VAR t : TypeDesc);
    BEGIN
      IF Compatible(t,PointerTo(chars)) THEN
        v.charValue := CHR(v.fixValue);
      ELSIF Compatible(t,PointerTo(ZZ)) THEN 
	(* a whole number type *)
        IF v.fixValue <= intMax THEN 
          t := PointerTo(ZZ);
        ELSIF IsSignedType(t) THEN 
          t := PointerTo(II);
        ELSE t := PointerTo(UU);
	END;
      (* ELSE don't meddle with it --- kjg Oct-89 *)
      END;
    END FixTypeAndValue;

    PROCEDURE IsOrdinalType(ty : TypeDesc) : BOOLEAN;
    BEGIN
      IF ty = NIL THEN RETURN TRUE;
      ELSE RETURN (ty^.tyClass IN TyClassSet
               {enums,chars,subranges,bools,cards,ints,II,ZZ,UU,S1})
      END;
    END IsOrdinalType;

    PROCEDURE IsOwnOpaque(id : IdDesc) : BOOLEAN;
    BEGIN
      IF id = NIL THEN RETURN FALSE END;
      RETURN (id^.idClass = typeNode) AND
             (id^.typType <> NIL) AND
             (id^.typType^.tyClass = opaqueTemp)
    END IsOwnOpaque;

(* ------------------------------------------------------------------------ *) 

PROCEDURE IsStringType (type : TypeDesc) : BOOLEAN;
(*
   New version for ISO semantics of Jun 1989 (kjg)
   index type must be an ordinal type 
   element type must be CHAR (not a subrange)
   lower bound is not longer necessarily zero
*)
BEGIN
  IF (type = NIL) OR 
     (type^.indexType = NIL) OR 
     (type^.elementType = NIL) THEN RETURN FALSE; (* avoid extra messages *)
  ELSE RETURN   (type^.tyClass = arrays) AND
		(type^.elementType = PointerTo(chars)) AND
		(type^.indexType^.tyClass IN 
		   TyClassSet{enums,chars,subranges,bools});
  END;
END IsStringType;

(* ------------------------------------------------------------------------ *) 

PROCEDURE StringLength(type : TypeDesc) : CARDINAL;
(*
  Return the length of the string type.
*)
BEGIN
  RETURN(type^.indexType^.maxRange+1
         - type^.indexType^.minRange)
END StringLength;

(* ------------------------------------------------------------------------ *) 

MODULE ExpressionCosts;
  IMPORT DStateType, EmptySelList, DesigRec, 
	SelectAttribute, InitDState, GetSelector,
	SelectNodeClass, Flags, TyNodeClass,
	InitCursor, Sequence, ElemPtr, Ended, GetNext,
        ActualParMode, ExprDesc, ExprNodeClass, bytesInWord;
	
  EXPORT HasCalls;

    PROCEDURE DesigCalls(des : DesigRec) : BOOLEAN;
      VAR dState : DStateType; 
	  selVal : SelectAttribute;
	  dCost  : CARDINAL; 
    BEGIN 
      IF EmptySelList(des) THEN RETURN FALSE;
      ELSE 
	InitDState(des,dState); 
	LOOP 
	  GetSelector(dState,selVal); 
	  IF selVal.tag = endMarker THEN RETURN FALSE;
	  ELSIF (selVal.tag = subscriptNode) AND
			HasCalls(selVal.exp) THEN RETURN TRUE;
	  END;
	END; (* loop *)
      END;
    END DesigCalls;

    PROCEDURE HasCalls(exp : ExprDesc) : BOOLEAN;
      VAR isHuge,bigSet : BOOLEAN;
    BEGIN
      isHuge := exp^.exprType^.tyClass = hInts;
      bigSet := (exp^.exprType^.tyClass = sets) AND
		(exp^.exprType^.size > bytesInWord);
      CASE exp^.exprClass OF
      | literalNode : RETURN FALSE;
      | andNode, orNode, plusNode, minusNode, equalsNode, notEqNode,
	greaterNode, grEqualNode, lessNode, lessEqNode :
	  IF bigSet THEN RETURN TRUE;
	  ELSE RETURN HasCalls(exp^.leftOp) OR HasCalls(exp^.rightOp);
	  END;
      | starNode, divNode, slashNode, modulusNode, remNode :
	  IF bigSet OR isHuge THEN RETURN TRUE;
	  ELSE RETURN HasCalls(exp^.leftOp) OR HasCalls(exp^.rightOp);
	  END;
      | notNode, negateNode : 
	  RETURN HasCalls(exp^.notOp);
      | castNode : 
	  RETURN HasCalls(exp^.source);
      | openMarshallNode, fixedMarshallNode :
	  RETURN HasCalls(exp^.actualX);
      | inNode, setDesigNode, constructorNode, funcDesigNode, preconNode : 
	  RETURN TRUE;
      | adrDesigNode, desigNode, selConstNode : 
	  RETURN DesigCalls(exp^.name);
      | errNode : RETURN FALSE;
      END;
    END HasCalls;

END ExpressionCosts;

(* ------------------------------------------------------------------------ *) 

PROCEDURE IsVariable (actual : ExprDesc) : BOOLEAN;
(*
  Determine if the actual parameter is a variable, and so acceptable as a 
  variable parameter.
  Code is similar to CheckDesignator, except that any designator has already
  been bound.
*)
VAR
  id : IdDesc;
BEGIN
  IF actual^.exprClass <> desigNode THEN
(*  Error(214);  let caller report error *)
    RETURN(FALSE)
  END;
  id := actual^.name.variable;
  RETURN((id <> NIL) AND (id^.idClass = varNode))
END IsVariable;

(* ------------------------------------------------------------------------ *) 

PROCEDURE UnivConform (actual, formal : TypeDesc) : BOOLEAN;
(*
  Determine if types actual & formal are compatible due to the universal 
  conformability of WORD, BYTE & ADDRESS formal parameters. Note that this 
  special case is not symmetric. 
*)

(* ! (tx<>NIL) AND (tx^.tyClass=y) as alternative to tx = PointerTo(y) ? *)

BEGIN
  (* Check formal for universal, and then against actual *)
  Assert (actual<>NIL);
  IF formal = PointerTo(words) THEN RETURN (actual^.size = wordSize)
  ELSIF formal = PointerTo(bytes) THEN
    RETURN (actual^.size = byteSize) OR (actual^.tyClass = S1);
  ELSIF formal = PointerTo(adrs) THEN
    RETURN (actual^.tyClass IN 
			TyClassSet{opaqueTemp,hiddens,pointers,stringTs}) 
  ELSE RETURN(FALSE)
  END
END UnivConform;

(* ------------------------------------------------------------------------ *) 

PROCEDURE AssignCompatible (lhsT,rhsT : TypeDesc) : BOOLEAN;
BEGIN
 (*
  *  Expression compatibility is good enough
  *)
  IF Compatible(lhsT,rhsT) THEN RETURN TRUE END;
 (*
  *  Also, INTEGER and CARDINAL are assignment-compatible 
  *  Assert: exprType and type are both <> NIL, since 
  *  otherwise Compatible would have returned TRUE
  *)
  IF lhsT^.tyClass = subranges THEN lhsT := lhsT^.hostType; END;
  IF rhsT^.tyClass = subranges THEN rhsT := rhsT^.hostType; END;
  RETURN (lhsT = PointerTo(cards)) AND (rhsT = PointerTo(ints)) OR
 	 (lhsT = PointerTo(ints)) AND (rhsT = PointerTo(cards));
END AssignCompatible;

PROCEDURE CheckedAssignCompatible (expr : ExprDesc; 
                                   type : TypeDesc;
                               VAR isOk : BOOLEAN);
(*
 *  Determine if expr(ession) is assignment-compatible with type.
 *  If not, return isOk FALSE; if so, perform compile-time range checks and
 *  return isOk TRUE.
 *)
VAR eType : TypeDesc; (* local for subrange expr host type *)
    tType : TypeDesc; (* local for subrange expr host type *)

BEGIN (* CheckedAssignCompatible *)
 (* Assert: expr <> NIL; exprType and/or type may be NIL *)

  isOk := AssignCompatible(type,expr^.exprType);

  (* And strings are assignment-compatible with string variables of equal or 
     greater length *)
  IF (NOT isOk) AND
     (expr^.exprClass = literalNode) AND
     (expr^.exprType^.tyClass IN TyClassSet{S1,SS}) AND
     IsStringType(type) THEN
    IF expr^.conValue.strHigh <= StringLength(type) THEN
      isOk := TRUE;
      EXCL (expr^.testFlags,rangeTests);
    END;
    RETURN;
  END;

  (* If no possibility succeeded - not compatible *)
  IF NOT isOk THEN RETURN; END;

  (* Compatible (perhaps due to NILs), but range tests should be checked *)
  eType := expr^.exprType;
  IF (eType<>NIL) AND (type<>NIL) THEN
    IF  (eType = type) OR 
	(eType^.tyClass IN TyClassSet{adrs,RR,procTypes,funcTypes}) OR
	(((eType^.tyClass = subranges) OR
	    (type^.tyClass = subranges)) AND
 	    TypesOverlap(type,eType)) OR
(*
 *  Note (16-Aug-89, kjg) some standard functions return ZZ which
 *  does not need runtime checking before assigning to cards or ints.
 *)
        ((eType^.tyClass = ZZ) AND 
	    ((type^.tyClass = cards) OR (type^.tyClass = ints))) THEN
(*
 *  Later, to check for floating point errors will need to
 *  check isnan(expr).
 *
 *  Maybe this should be done explicitly under programmer
 *  control, since nans propagate correctly.
 *  Say, a procedure FPCheck, with body
 *	IF isnan(val) THEN Exceptions.Raise(fpError) END;
 *)
      EXCL (expr^.testFlags,rangeTests);
      EXCL (expr^.testFlags,indexTests);
    ELSIF type^.tyClass = hInts THEN
      EXCL(expr^.testFlags, rangeTests);
    ELSIF expr^.exprClass=literalNode THEN
      RangeCheckC (expr^, type);
    (* else runtime check needed *)
    END;
  END;
END CheckedAssignCompatible;

(* ------------------------------------------------------------------------ *) 

PROCEDURE ValOpenCompatible(actuTy : TypeDesc; 
			    formTy : FormalType) : ActualParMode;
(*
 * Check if actual parameter of type actuTy is compatible with formal open 
 * array parameter of element type elemTy. Return the actual parameter mode -
 * open1D for normal open arrays, openWord or openByte for the universally
 * conformable parameters, and notActual for errors.
 * Multi-dimensional open arrays are now treated.
 *)
  VAR elemTy : TypeDesc;
      dIndex : CARDINAL;
BEGIN
  elemTy := formTy^.type;
  IF elemTy = NIL THEN RETURN(notActual) END;
  IF formTy^.dimN = 1 THEN
    IF elemTy^.tyClass = words THEN
      RETURN wordOpen;		(* no need to align with marshalling! *)
    ELSIF elemTy^.tyClass = bytes THEN 
      RETURN byteOpen;
    ELSIF actuTy^.tyClass IN TyClassSet{arrays,SS,S1} THEN
      IF AssignCompatible(elemTy,actuTy^.elementType) THEN 
						RETURN(open1D) END;
      Error(257);
    ELSE Error(256);
    END;
    RETURN(notActual);
  ELSE (* multi-dim *)
    FOR dIndex := 1 TO formTy^.dimN DO
      IF actuTy^.tyClass = arrays THEN 
	actuTy := actuTy^.elementType;
      ELSE 
	Error(256);
      END;
    END;
    IF AssignCompatible(elemTy,actuTy) THEN RETURN(open1D) END;
    Error(257); RETURN(notActual);
  END;
END ValOpenCompatible;

(* ------------------------------------------------------------------------ *) 

PROCEDURE VarOpenCompatible(actuTy : TypeDesc; 
			    formTy : FormalType) : ActualParMode;
(*
 * Check if actual parameter of type actuTy is compatible with formal open 
 * array parameter of element type elemTy. Return the actual parameter mode -
 * open1D for normal open arrays, openWord or openByte for the universally
 * conformable parameters, and notActual for errors.
 * Multi-dimensional open arrays are now treated.
 *)
  VAR elemTy : TypeDesc;
      dIndex : CARDINAL;
BEGIN
  elemTy := formTy^.type;
  IF elemTy = NIL THEN RETURN(notActual) END;
  IF formTy^.dimN = 1 THEN
    IF elemTy^.tyClass = words THEN
      IF (actuTy^.tyClass <> stringTs) AND
         (actuTy^.alignMask < alignMap[bytesInWord]) THEN Error(307) END;
(*
 *       (actuTy^.alignMask <= alignMap[bytesInWord]) THEN Error(307) END;
 *)
      RETURN wordOpen;
    ELSIF elemTy^.tyClass = bytes THEN 
      RETURN byteOpen;
    ELSIF actuTy^.tyClass = arrays THEN
      IF actuTy^.elementType <> elemTy THEN Error(257) END;
      RETURN open1D;
    ELSIF actuTy^.tyClass = stringTs THEN
      IF actuTy^.elementType <> elemTy THEN Error(257) END;
      RETURN open1D; 
    ELSE Error (256);
    END;
    RETURN(notActual);
  ELSE (* multi-dim *)
    FOR dIndex := 1 TO formTy^.dimN DO
      IF actuTy^.tyClass = arrays THEN 
        actuTy := actuTy^.elementType;
      ELSE 
        Error(256);
      END;
    END;
    IF AssignCompatible(elemTy,actuTy) THEN RETURN(open1D) END;
    Error(257); RETURN(notActual);
  END;
END VarOpenCompatible;

(* ------------------------------------------------------------------------ *) 
      PROCEDURE CheckValidAllocate(allPrc : IdDesc);
      (*
         kjg 24-Mar-89 -- check that allPrc is a valid allocation
         procedure suitable for substitution for NEW or DISPOSE
         Later, it might be worth memo-izing the result since
         the same procs will be checked over and over ...
      *)
        VAR fCrs : ElemPtr;
            frm1, frm2 : FormalType;
      BEGIN
        IF allPrc^.idClass IN 
             IdClassSet{procHeader,procNode,externProc} THEN
          InitCursor(allPrc^.procType^.params,fCrs);
          IF NOT Ended(fCrs) THEN
            GetNext(fCrs,frm1);
            IF NOT Ended(fCrs) THEN
              GetNext(fCrs,frm2);
              IF  Ended(fCrs)                  AND
                 (frm1^.form = varForm)        AND
                 (frm1^.type^.tyClass = adrs)  AND
                 (frm2^.form = valForm)        AND
                 (frm2^.type^.tyClass = cards) THEN RETURN (* ok *)
              END;
            END;
          END;
        END;
        ErrIdent(284,allPrc^.name);
      END CheckValidAllocate;

(* ------------------------------------------------------------------------ *) 

PROCEDURE IndexCheckC (VAR expr : ExprRec; typ : TypeDesc);

(* 
  Check if a constant index value is in the range of the index type typ.
  Precondition: expr is a literalNode Compatible with typ.
  Postcondition: error detected, or no runtime check needed.
*)
VAR min, max : CARDINAL;  (* limits of index type *)
BEGIN
  min := MinOfOrdType(typ);
  max := MaxOfOrdType(typ);
  IF typ^.tyClass=subranges THEN typ := typ^.hostType; END;
  WITH expr DO
    CASE typ^.tyClass OF
    | bools, enums, cards : (* unsigned word arithmetic *)
        IF (conValue.fixValue < min) OR (conValue.fixValue > max) THEN
          Error (215); RETURN;
        END;
    | chars : (* unsigned byte arithmetic *)
        IF (conValue.charValue < CHR(min)) OR
           (conValue.charValue > CHR(max)) THEN
          Error (215); RETURN;
        END;
    | ints :
        IF (conValue.intValue < CAST(INTEGER,min)) OR
           (conValue.intValue > CAST(INTEGER,max)) THEN 
          Error (215); RETURN;
        END;
    END;
    (* If no error, indicate that no runtime check is needed *)
    EXCL(testFlags, indexTests);
  END;
END IndexCheckC ;

(* ------------------------------------------------------------------------ *) 
      PROCEDURE TypesOverlap(dstTyp : TypeDesc;
                             srcTyp : TypeDesc) : BOOLEAN;

        TYPE TrickWord = RECORD
                           CASE : BOOLEAN OF
                           | TRUE  : c : CARDINAL;
                           | FALSE : i : INTEGER;
                           END;
                         END;

        VAR  dSgnd  : BOOLEAN;
             dMin, dMax, sMin, sMax : TrickWord;
      BEGIN
        dSgnd  := IsSignedType(dstTyp);
        dMin.c := MinOfOrdType(dstTyp);
        dMax.c := MaxOfOrdType(dstTyp);
        sMin.c := MinOfOrdType(srcTyp);
        sMax.c := MaxOfOrdType(srcTyp);
        (*
           calculate overlap expressed in srcTyp terms
        *)
        IF IsSignedType(srcTyp) THEN (* signed source *)
          IF NOT dSgnd THEN (* x.i < 0 ==> x.c > intMax *)
            IF dMin.i < 0 THEN Error(285); RETURN FALSE;
            ELSIF dMax.i < 0 THEN dMax.i := sMax.i;
            END;
          END;
          IF (sMax.i <= dMax.i) AND (sMin.i >= dMin.i) THEN
            RETURN TRUE;
          END;
        ELSE (* unsigned source *)
          IF dSgnd THEN
            IF dMax.i < 0 THEN Error(285); RETURN FALSE;
            ELSIF dMin.i < 0 THEN dMin.c := 0;
            END;
          END;
          IF (sMin.c >= dMin.c) AND (sMax.c <= dMax.c) THEN
            RETURN TRUE;
          END;
        END;
        RETURN FALSE;
      END TypesOverlap;
(* ------------------------------------------------------------------------ *) 
    PROCEDURE LiteralInRange(dstTyp : TypeDesc;
                             VAR litExp : ExprRec) : BOOLEAN;
    (*
     *  pre  : litExp must be literal, dstTyp must be ordinal
     *  post : result = "value is enclosed in destination range"
     *)
      VAR min, max : CARDINAL;
    BEGIN
      min := MinOfOrdType(dstTyp);
      max := MaxOfOrdType(dstTyp);
      IF dstTyp^.tyClass=subranges THEN dstTyp := dstTyp^.hostType; END;
      WITH dstTyp^ DO
       (* First the special cases of assignment compatibility *)
        IF (tyClass = ints) AND
           (litExp.exprType^.tyClass = UU) THEN RETURN FALSE;
        ELSIF
           (tyClass = cards) AND
           (litExp.exprType^.tyClass = II) THEN RETURN FALSE;
        END;
        (* Now the range check in the appropriate arithmetic *)
        CASE tyClass OF
        | bools, enums, cards : 
            RETURN (litExp.conValue.fixValue >= min) AND 
                   (litExp.conValue.fixValue <= max);
        | chars : 
            RETURN (litExp.conValue.charValue >= CHR(min)) AND 
                   (litExp.conValue.charValue <= CHR(max));
        | ints : 
            RETURN (litExp.conValue.intValue >= CAST(INTEGER,min)) AND 
                   (litExp.conValue.intValue <= CAST(INTEGER,max));
        END; (* case *)
      END; (* with *)
    END LiteralInRange;

(* ------------------------------------------------------------------------ *) 

PROCEDURE RangeCheckC (VAR expr : ExprRec; ordTyp : TypeDesc);
(* 
  Check if a constant value is in the range of the type ordTyp.
  Precondition: expr is a literalNode AssignCompatible with ordinal type
  ordTyp.
  Postcondition: error detected, or no runtime check needed.
*)
BEGIN
  Assert (IsOrdinalType(ordTyp));
  IF LiteralInRange(ordTyp,expr) THEN
    EXCL(expr.testFlags, rangeTests);
    EXCL(expr.testFlags, indexTests);
  ELSE Error(215);
  END;
END RangeCheckC ;

PROCEDURE Align (oldSize : CARDINAL; quadAlign : CHAR) : CARDINAL;
(* Return oldSize rounded up, if necessary, to the next boundary
   corresponding to alignment *)
BEGIN
  RETURN CAST(
               CARDINAL,
               (
                 CAST(BITSET,oldSize + ORD(quadAlign)) - 
                 CAST(BITSET,ORD(quadAlign))
               )
             );
END Align;
  
PROCEDURE AlignAndAdd (VAR rTy : TypeDesc;
                       addAlignment : CHAR; addSize : CARDINAL);
(* Increase the size of record type rTy^ to begin the next component at an
   addAlignment boundary; then add a component of addSize to the record size;
   also upgrade rTy^'s overall alignment if necessary.
*)
BEGIN
  WITH rTy^ DO
    size := Align(size,addAlignment) + addSize;
    IF addAlignment>alignMask THEN alignMask := addAlignment; END;
  END;
END AlignAndAdd ;

PROCEDURE MaxSizeAndAlignment (VAR unTp : TypeDesc; vTp : TypeDesc);
(* Make the size and alignment of the union type unTp^ the maximum of their
   current values and those of the variant vTp^.
*)
BEGIN
  IF vTp^.size > unTp^.size THEN unTp^.size := vTp^.size END;
  IF vTp^.alignMask > unTp^.alignMask THEN
    unTp^.alignMask := vTp^.alignMask
  END;
END MaxSizeAndAlignment;

    PROCEDURE BindFieldOffsets(VAR recRec : TypeRec);
    (* Precondition  : size and alignMask fields have been set 
                       recRec is a fully formed errorless TyRec  
       Postcondition : fieldOffset fields are inserted in descr. *)

        (*   (* low-level diagnostics commented out *)
             VAR fName : ARRAY[0 .. 39] OF CHAR; ix : CARDINAL;
                 depth : CARDINAL;
        *)

      PROCEDURE FieldList(start : CARDINAL; seq : Sequence);
        (* seq is a sequence of idDesc *)
	VAR curs  : ElemPtr;
	    field : IdDesc;
      BEGIN
	(*
	    INC(depth,2);
	*)
	InitCursor(seq,curs);
        WHILE NOT Ended(curs) DO
	  GetNext(curs,field);
	  WITH field^ DO
	    (*
		align each field as required
	    *)
	    start := CAST(CARDINAL,
			   CAST(BITSET,start + ORD(fieldType^.alignMask))
			 - CAST(BITSET, ORD(fieldType^.alignMask))
			  );
	    fieldOffset := start;
	    (*
		IF field^.fieldType^.tyClass <> unions THEN
		fName := "                                 ";
		ix := depth;
		GetSourceRep(name,fName,ix);
		WriteString(fName);
		WriteCard(start,3);
		WriteCard(field^.fieldType^.size,3);
		WriteLn;
		END;
	    *)
	    IF field^.fieldType^.tyClass = unions THEN
	      DoVariants(start,field^.fieldType);
	    END;
	    INC(start,fieldType^.size);
	  END; (* with *)
	END; (* while *)
	(*
	    DEC(depth,2);
	*)
      END FieldList;

      PROCEDURE DoVariants(start : CARDINAL; oneOf : TypeDesc);
	VAR curs    : ElemPtr;
	    variant : TypeDesc;
      BEGIN
	(*
	   align whole union on the most restrictive boundary
	*)
	start := CAST(CARDINAL,
			   CAST(BITSET,start + ORD(oneOf^.alignMask))
			 - CAST(BITSET, ORD(oneOf^.alignMask))
		     );
	InitCursor(oneOf^.varSeq,curs);
        WHILE NOT Ended(curs) DO
	  (*
		WriteCard(depth DIV 2,1);
		WriteString(" var start");
		WriteLn;
	  *)
	  GetNext(curs,variant);
	  FieldList(start,variant^.fieldSeq);
	  (*
		WriteCard(depth DIV 2,1);
		WriteString(" var end"); WriteLn;
	  *)
        END;
      END DoVariants;

    BEGIN
      (*
	depth := 0; WriteLn; WriteLn;
      *)
      FieldList(0,recRec.fieldSeq);
    END BindFieldOffsets;

END M2SSUtilities.

