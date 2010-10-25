(****************************************************************)
(*                                                              *)
(*             Modula-2 Compiler Source Module                  *)
(*                                                              *)
(*          Symbol File Parser and Tree Constructor.            *)
(*                                                              *)
(*     (c) copyright 1988 Faculty of Information Technology     *)
(*                                                              *)
(*      original module : kjg march 1988                        *)
(*      modifications   : 12-Mar-88                             *)
(*      last modified   : 20-Sep-88, check imp/exp of procvars  *)
(*			:  7-Nov-89  alignment of types		*)
(*					and field offset values *)
(*		        : 29-Jan-90  fix in ConProc		*)
(*			: 30-Mar-90  16 subranges now ok	*)
(*			:  2-Apr-90   8 subranges now ok	*)
(*			: 11-Apr-90  reference RelaxLexical...  *)
(*			: 17-Apr-90  fix error in enum synons   *)
(*			: 13-Jul-90  fix opaque alias code      *)
(*			: 13-Jul-90  Insert semantics mutatis   *)
(*			:  8-Sep-90  Fix indirect circular refs *)
(*			:  8-Sep-90  uses M2Machine alignMap    *)
(*			: 13-Apr-91  fix import of set of anon  *)
(*			:    Feb-92  circular import of opaques *)
(*			:    Mar-92  import own symbols		*)
(*			: 12-Apr-92  jrh CheckElab fwd imports  *)
(*                                                              *)
(****************************************************************
$Log: m2sympar.mod,v $
Revision 1.8  1997/01/16 05:17:06  gough
major restructuring.  New facilities for reading and writing
precondition expressions in the symbol file.

Revision 1.7  1996/11/27 03:00:29  lederman
remove calc. of some obsolete modState info.

Revision 1.6  1996/07/30 00:09:12  gough
write and parse string types

Revision 1.5  1995/10/10 23:56:04  lederman
tidy up

# Revision 1.4  1995/03/23  23:09:31  gough
# symbol files may now have multidimensional open arrays
#
# Revision 1.3  1995/03/17  02:58:33  lederman
# remove version checking - so that you can mix version 2 & 3 if you want
#
# Revision 1.2  1994/07/01  05:38:10  lederman
# import versionNumber form M2Machine
#
# Revision 1.1  1994/04/07  05:25:35  lederman
# Initial revision
#
*****************************************************************
Revision 1.6  93/11/16  09:01:02  gough
put optional retCut marker in symbol file format

Revision 1.5  93/11/15  17:40:20  gough
initial revision. some cleanup of definition prior to changes
*****************************************************************)

IMPLEMENTATION MODULE M2SymParser;

(* ------------------------------------------------------------ *
 *   Unit = Header [ Kind ] ModuleImports SymbolModule 		*
 *  		          ImportObjects keySy eofSy .		*
 *   Header        = VersionNumber ident.			*
 *   Kind          = (nilSy | bar | fromSy) [upArrow] .		*
 *   ModuleImports = lBrac {ident keySy} rBrac .		*
 *   SymbolModule  = moduleSy { Definition } endSy .		*
 *   ImportObjects = importSy { Definition } endSy .		*
 * ------------------------------------------------------------ *
 *  Note that the ImportObjects are written out only for types  *
 *  but that they are simply skipped over when reading. This 	*
 *  reflects a semantic change, and could be removed. However 	*
 *  it provides some additional key checking safety maybe.	*
 * ------------------------------------------------------------ *)

IMPORT StdError, SYSTEM;

FROM M2NodeDefs  IMPORT 
        IdDesc, IdTree, IdNodeClass, IdClassSet, CreateIdDesc, InsertRef, 
        TypeDesc, TyNodeClass, CreateTypeDesc, SuspendList,
        ResumeList, FormalType, FormalClass, FormalRec,
        MakeFormal, modState, Attribute, AttributeSet,
        globalModList, thisCompileUnit, pervasiveUnit,
        unitImports, unitExports, symKeyValue, TreeRec,
	StandardProcs, current, PubEnum;

FROM M2Alphabets IMPORT 
	TerminalSymbols, SymbolSet, Spellix,
        Flags, FlagSet, ModStateFlags, ModStateSet,
        errors, HashBucketType, LexAttType, ConBlock;

FROM M2NameHandler IMPORT 
	SpellingIndex, DumpBytes, GetSourceRep, EnterString, anonBkt, stdBkt;

FROM M2MachineConstants IMPORT 
	alignMap, bytesInWord, bytesInReal, nilValue, 
	minVersion, refVersion, symVersion;

FROM M2Scanner   IMPORT 
	lexAtt, CurrentFlags, SetFlagOn, RelaxLexicalRules,
        symSmbl, GetSymSmbl, PshSymScanState, PopSymScanState;

FROM M2InOut     IMPORT 
	WriteSb, CreateNewSymFile, CloseNewSymFile,
	ReadSb, Error, ErrIdent, WriteSymbolKey,
	OpenOldSymFile, CloseOldSymFile,
	DiagName, lastPos, Position,
	AbortMessage, SymbolMessage, ListKey;

FROM M2Designators IMPORT
	ExprDesc, ExprNodeClass, DesigRec, CreateExprDesc,
	EmptySelList, InitDState, GetSelector, DStateType, 
	PushIdentifier, PushDereference, PushSubscript,
	SelectListBegin, SelectListEnd, SelectNodeClass, SelectAttribute;

FROM GenSequenceSupport IMPORT 
	Sequence, ElemPtr, LinkLeft, LinkRight, InitCursor, GetNext,
	InitSequence, NextIsLast, Ended, DisposeList;

FROM M2SSUtilities IMPORT 
	BindFieldOffsets, LookupInThisScope, LookupInModList;

FROM M2StructureDefs IMPORT RangeDesc, MakeRangeDesc;

FROM M2TabInitialize IMPORT PointerTo;

FROM M2NamGenerate   IMPORT MakeTempName, MakeLinkerName;

FROM ProgArgs IMPORT Assert;

(* ------------------------------------------------------------ *
 * ------------------------------------------------------------ *
 * The symbolfile writer is unchanged from the previous version *
 * ------------------------------------------------------------ *
 * ------------------------------------------------------------ *)

  MODULE SymbolFileWriter;
  IMPORT StdError, SYSTEM, DiagName;
  IMPORT ExprDesc, ExprNodeClass, DStateType, CreateIdDesc,
	 EmptySelList, InitDState, GetSelector, MakeTempName,
	 RangeDesc, SelectNodeClass, SelectAttribute;
  IMPORT InitCursor, Ended, ElemPtr, GetNext, IdTree,
         IdDesc, IdNodeClass, TypeDesc, TyNodeClass,
         thisCompileUnit, globalModList, unitImports,
         unitExports, anonBkt, bytesInReal, bytesInWord,
         LexAttType, errors, refVersion, symVersion, stdBkt, ConBlock,
         DumpBytes, WriteSb, Assert, Sequence, librarySpx,
         CreateNewSymFile, CloseNewSymFile, WriteSymbolKey,
         CurrentFlags, Flags, FlagSet, SpellingIndex,
         HashBucketType, Spellix, TerminalSymbols,
         FormalClass, FormalType, FormalRec,
         modState, ModStateFlags, ModStateSet;

  EXPORT MakeSymbolFile, DefCon, DumpTypeDesc;

    VAR dumpMod  : HashBucketType;
        lastType : TypeDesc;

    (* The following code is endian-insensitive   *)
    (* cardinals are ALWAYS written out lsb first *)

    PROCEDURE EmitFixNum(nm : CARDINAL);
      VAR ix : CARDINAL;
    BEGIN
      WriteSb(fixNum);
      FOR ix := 1 TO bytesInWord DO
        WriteSb(CHR(nm MOD 400B)); nm := nm DIV 400B;
      END;
    END EmitFixNum;

    PROCEDURE EmitKeyNum(nm : CARDINAL);
      VAR ix : CARDINAL;
    BEGIN
      WriteSb(keySy);
      FOR ix := 1 TO bytesInWord DO
        WriteSb(CHR(nm MOD 400B)); nm := nm DIV 400B;
      END;
    END EmitKeyNum;

    PROCEDURE MakeHeader();
    BEGIN
      IF extensions IN modState THEN
	EmitFixNum(symVersion);
      ELSE
	EmitFixNum(refVersion);
      END;
      WriteSb(ident); DumpBytes(SpellingIndex(dumpMod),0);
    END MakeHeader;

    PROCEDURE EmitIdent(idBkt : HashBucketType);
    BEGIN
      WriteSb(ident); DumpBytes(SpellingIndex(idBkt),0);
    END EmitIdent;

    PROCEDURE EmitMarker(modBkt : HashBucketType);
    BEGIN
      IF modBkt = dumpMod THEN WriteSb(dot);
      ELSIF modBkt = stdBkt THEN WriteSb(slash);
      ELSE
        EmitIdent(modBkt);
        WriteSb(dot);
      END;
    END EmitMarker;

    PROCEDURE DumpFields(tPtr : TypeDesc);
      VAR curs : ElemPtr; iPtr : IdDesc;
    BEGIN
      InitCursor(tPtr^.fieldSeq,curs);
      WHILE NOT Ended(curs) DO
        GetNext(curs,iPtr);
        WITH iPtr^ DO
          IF name <> anonBkt THEN (* an ordinary field *)
            EmitIdent(name); 
(*
 * #ifdef FIELDOFFSETS
 *	    DiagName(name);
 *	    StdError.WriteCard(iPtr^.fieldOffset,4);
 *	    StdError.WriteCard(ORD(iPtr^.fieldType^.alignMask),2);
 *	    StdError.WriteLn;
 * #endif
 *)
          END; (* else a union type *)
          DumpTypeDesc(fieldType);
        END;
      END;
    END DumpFields;

    PROCEDURE DumpTypeDesc(tPtr : TypeDesc);
      VAR curs : ElemPtr; vPtr : TypeDesc;
          iPtr : IdDesc;  fPtr : FormalType;
          ix   : CARDINAL;
    BEGIN
      IF tPtr = lastType THEN WriteSb(equals);
      ELSE
        WITH tPtr^ DO
          IF dumped THEN (* write QualIdent *)
            EmitMarker(parentMod^.name); EmitIdent(tyName);
          ELSE (* NOT dumped *)
            IF tyName = anonBkt THEN WriteSb(nilSy);
            ELSE
              WriteSb(plus); dumped := TRUE;
              EmitMarker(parentMod^.name); EmitIdent(tyName);
            END;
            CASE tyClass OF
            | enums :
                WriteSb(lPar); InitCursor(conSeq,curs);
                FOR ix := 1 TO cardinality DO
                  GetNext(curs,iPtr); 
                  EmitIdent(iPtr^.name);
                END;
                WriteSb(rPar);
            | subranges :
                WriteSb(lBrac); EmitFixNum(minRange);
                EmitFixNum(maxRange); DumpTypeDesc(hostType);
                WriteSb(rBrac);
            | arrays :
                WriteSb(arraySy); DumpTypeDesc(indexType);
                WriteSb(ofSy); DumpTypeDesc(elementType);
            | sets : WriteSb(setSy); DumpTypeDesc(baseType);
            | hiddens, opaqueTemp : WriteSb(notEq);
            | pointers :
                WriteSb(pointerSy); DumpTypeDesc(targetType);
            | stringTs :
                WriteSb(stringSy);  DumpTypeDesc(targetType);
            | records :
                WriteSb(recordSy); DumpFields(tPtr); WriteSb(endSy);
            | unions :
                WriteSb(caseSy); InitCursor(varSeq,curs);
                WHILE NOT Ended(curs) DO
                  GetNext(curs,vPtr); (* vPtr^ is a record desc. *)
                  WriteSb(bar); DumpFields(vPtr);
                END;
                WriteSb(endSy);
            | procTypes, funcTypes :
                WriteSb(procedureSy); WriteSb(lPar);
                InitCursor(params,curs);
                WHILE NOT Ended(curs) DO
                  GetNext(curs,fPtr);
                  WriteSb(charNum); WriteSb(fPtr^.form);
		  IF (fPtr^.form >= openValForm) AND
		     (fPtr^.dimN > 1) THEN
                    WriteSb(charNum); WriteSb(CHR(fPtr^.dimN));
		  END;
(* this version does not dump the ".name" fields *)
                  DumpTypeDesc(fPtr^.type);
                END;
                WriteSb(rPar);
                IF result <> NIL THEN
                  WriteSb(colon); DumpTypeDesc(result);
                END;
		IF preCon <> NIL THEN WritePreconExpr(tPtr) END;
            END; (* case *)
            EmitFixNum(size);
          END; (* not dumped *)
        END; (* with *)
      END; (* else *)
      lastType := tPtr;
    END DumpTypeDesc;

    PROCEDURE DefCon(iPtr : IdDesc);
      VAR conClass : TyNodeClass;
	  cPtr     : ConBlock;
	  ix       : CARDINAL;
    BEGIN
      WITH iPtr^ DO
	conClass := conType^.tyClass;
	WriteSb(constSy);
	EmitIdent(name);
	CASE conClass OF
	| II, ZZ, UU, bools, ints, cards, words, bytes, enums, subranges :
	    EmitFixNum(conValue.fixValue);
	    WriteSb(charNum); WriteSb(conType^.tyClass);
	    IF (conClass = enums) OR
	       (conClass = subranges) THEN DumpTypeDesc(conType) END;
	| sets: 
	    WriteSb(bigSetCon); WriteSb(CHR(conType^.size));
	    DumpBytes(conValue.patternIx,conType^.size);
	    DumpTypeDesc(conType);
	| records, arrays :
	    cPtr := conValue.adrsValue;
	    WriteSb(heapConst); 
	    EmitFixNum(conType^.size);
	    FOR ix := 0 TO conType^.size - 1 DO WriteSb(cPtr^[ix]) END;
	    DumpTypeDesc(conType);
        | floats, doubles, RR : 
	    WriteSb(floatNum);
            FOR ix := 0 TO bytesInReal - 1 DO WriteSb(conValue.bytes[ix]) END;
        | SS : WriteSb(litstring); DumpBytes(conValue.stringIx,0);
        | chars : WriteSb(charNum); WriteSb(conValue.charValue);
        | S1 : WriteSb(charLit); WriteSb(conValue.charValue);
        | adrs  : WriteSb(nilSy);
            (* more if other address constants are to be allowed *)
        END;
      END;
    END DefCon;

    PROCEDURE DumpIdDesc(iPtr : IdDesc);
    BEGIN
      WITH iPtr^ DO
        CASE idClass OF
        | constNode :
	    DefCon(iPtr);
        | typeNode :
            WriteSb(typeSy);
            EmitIdent(name);
            DumpTypeDesc(typType);
        | varNode :
            WriteSb(varSy);
            EmitIdent(name);
           (* ========================================================= *)
           (* ====== optional aliases in interface symbol files ======= *)
           (* ========================================================= *)
            IF (directMod IN modState) AND
                 (varOffset <> 0) THEN
              WriteSb(litstring); 
              DumpBytes(varOffset,0);
            END;
           (* ========================================================= *)
            DumpTypeDesc(varType);
        | procHeader, externProc, procNode :
            WriteSb(procedureSy);
            EmitIdent(name);
           (* ========================================================= *)
           (* ====== optional aliases in interface symbol files ======= *)
           (* ========================================================= *)
            IF (directMod IN modState) AND
               (extAlias <> 0) THEN
              WriteSb(litstring); 
              DumpBytes(extAlias,0);
            END;
           (* ========================================================= *)
            DumpTypeDesc(procType);
        | exportNode : (* The semantics are unclear here. Should
                          these objects become visible in the imp.
                          part or not? Can't say at this stage   *)
        | conProc : 
            WriteSb(upArrow);
            EmitIdent(name);
            CASE procId^.idClass OF
            | stProc, stFunc :
                WriteSb(charNum);
                WriteSb(procId^.idClass);
                WriteSb(charNum);
                WriteSb(procId^.procVal);
            | externProc : 
                EmitIdent(procId^.module^.name);
                WriteSb(dot);
                DumpIdDesc(procId);
                IF procId^.nonLeaky THEN WriteSb(bar) END;
            ELSE (* procHeader, procNode *)
              WriteSb(dot); 
              DumpIdDesc(procId);
            END; (* case *)
        END; (* case *)
      END; (* with iPtr^ *)
    END DumpIdDesc;

    PROCEDURE MakeSymbolFile();
      VAR curs : ElemPtr; iPtr : IdDesc;
    BEGIN
      Assert(CurrentFlags() * errors = FlagSet{});
      dumpMod := thisCompileUnit^.name;
      CreateNewSymFile(dumpMod);
      MakeHeader;
      (* this next marks !SYSTEM and !NONREC modules *)
      IF sysMod IN modState THEN WriteSb(nilSy);
      ELSIF macroMod IN modState THEN 
	WriteSb(fromSy);
	IF librarySpx <> 0 THEN
          WriteSb(litstring); 
	  DumpBytes(librarySpx,0);
	END;
	IF directMod IN modState THEN WriteSb(forSy) END;
      ELSIF nonRec IN modState THEN WriteSb(bar);
      END;
      IF retCutAll IN modState THEN WriteSb(upArrow) END;
      WriteSb(lBrac);
      InitCursor(globalModList,curs);
      WHILE NOT Ended(curs) DO
        GetNext(curs,iPtr);
	(*
	 *   don't write out unloaded symbol modules
	 *)
	IF NOT iPtr^.system THEN 
	  EmitIdent(iPtr^.name);
	  EmitKeyNum(iPtr^.keyValue);
	END;
      END;
      WriteSb(rBrac); WriteSb(moduleSy);
      InitCursor(unitExports,curs);
      WHILE NOT Ended(curs) DO
        GetNext(curs,iPtr); 
        DumpIdDesc(iPtr);
      END;
      WriteSb(endSy); WriteSb(importSy);
      InitCursor(unitImports,curs);
      WHILE NOT Ended(curs) DO
        GetNext(curs,iPtr);
        IF iPtr^.idClass = typeNode THEN DumpIdDesc(iPtr) END;
      END;
      WriteSb(endSy);
      WriteSb(keySy);
      WriteSymbolKey(); (* accumulated in M2InOut *)
      WriteSb(eofSy);
      CloseNewSymFile();
    END MakeSymbolFile;


    PROCEDURE PutDesignator(des : ExprDesc);
      VAR dState : DStateType;
	  attrib : SelectAttribute;
	  pIndex : CARDINAL;
    BEGIN
      WITH des^ DO
	IF name.variable^.idClass = posParNode THEN	(* Parameter  *)
	  EmitFixNum(name.variable^.posIndex);
	ELSE
	  IF name.variable^.varClass = extern THEN	(* extern Var *)
	    EmitIdent(name.variable^.origMod^.name); 
	    WriteSb(dot);
	  END;
	  EmitIdent(name.variable^.name);		(* qualifName *)
	END;
	IF NOT EmptySelList(des^.name) THEN
	  InitDState(name,dState);
	  LOOP
	    GetSelector(dState,attrib);
	    CASE attrib.tag OF
	    | endMarker        : EXIT;
	    | fieldExtractNode : EmitIdent(attrib.fid^.name);
	    | subscriptNode    : WriteSb(lBrac); PutExp(attrib.exp);
	    | dereferenceNode  : WriteSb(upArrow);
	    END;
	  END;
	END;
	WriteSb(endSy);
      END;
    END PutDesignator;

    PROCEDURE DumpLiteral(exp : ExprDesc);
      VAR id : IdDesc;
    BEGIN
      CreateIdDesc(anonBkt,id,constNode);
      MakeTempName(id);
      id^.conValue := exp^.conValue;
      id^.conType  := exp^.exprType;
      DefCon(id);
    END DumpLiteral;

    PROCEDURE PutFuncCall(exp : ExprDesc);
      VAR curs : ElemPtr;
	  parX : ExprDesc;
    BEGIN
      PutDesignator(exp);
      WriteSb(lPar);
      InitCursor(exp^.paramSeq,curs);
      WHILE NOT Ended(curs) DO
	GetNext(curs,parX);
	PutExp(parX);
      END;
      WriteSb(rPar);
    END PutFuncCall;

    PROCEDURE PutRanges(exp : ExprDesc);
      VAR curs : ElemPtr;
	  rnge : RangeDesc;
    BEGIN
      WriteSb(lCurly);
      InitCursor(exp^.rangeSeq,curs);
      WHILE NOT Ended(curs) DO
	GetNext(curs,rnge);
	PutExp(rnge^.lower);
	IF rnge^.upper = NIL THEN WriteSb(nilSy) ELSE PutExp(rnge^.upper) END;
      END;
      WriteSb(rCurly);
    END PutRanges;

    PROCEDURE PutExp(exp : ExprDesc);
      VAR class : ExprNodeClass;
    BEGIN
      class := exp^.exprClass;
      IF class = literalNode THEN DumpLiteral(exp);
      ELSE (* not a literal *)
	WriteSb(class);
	IF class <= negateNode THEN (* unary and binary ops *)
	  PutExp(exp^.leftOp);
	  IF class <= inNode THEN PutExp(exp^.rightOp) END;
	ELSE
	  CASE class OF
	  | desigNode       : PutDesignator(exp);
	  | constructorNode, 
	    setDesigNode    : PutRanges(exp);
	  | adrDesigNode    : Assert(FALSE);
	  | funcDesigNode   : PutFuncCall(exp);
	  END;
	END;
	DumpTypeDesc(exp^.exprType);
      END;
    END PutExp;

    PROCEDURE WritePreconExpr(typ : TypeDesc);
    BEGIN
      WriteSb(preconSy);
      PutExp(SYSTEM.CAST(ExprDesc,typ^.preCon));
    END WritePreconExpr;

  BEGIN
    lastType := NIL;
  END SymbolFileWriter;

(* ----------------------------------------------------- *)

  MODULE AnonHandler;
    IMPORT HashBucketType, TyNodeClass, GetSourceRep, EnterString, IdDesc;
    EXPORT InitAnons, newAnonBkt, ptrTargetName;

    TYPE  Map = ARRAY [0 .. 15] OF CHAR;

    CONST max = 4095;
          hex = Map{'0','1','2','3','4','5','6','7',
                    '8','9','a','b','c','d','e','f'};

    CONST ptrSuffix = "-Deref";

    VAR count  : CARDINAL;
        name   : ARRAY [0 .. 13] OF CHAR;
        ptrBkt : HashBucketType;

    PROCEDURE InitAnons();
    BEGIN
      EnterString(ptrSuffix, ptrBkt);
      count := 1;
    END InitAnons;

    PROCEDURE newAnonBkt(tag : TyNodeClass) : HashBucketType;
      VAR tNum : CARDINAL;
          tHsh : HashBucketType;
    BEGIN
      tNum := count;
      CASE tag OF
      | sets    : name := "Pblc$SetTxxxx";
      | enums   : name := "Pblc$Enumxxxx";
      | arrays  : name := "Pblc$ArrTxxxx";
      | records : name := "Pblc$RecTxxxx";
      ELSE        name := "Pblc$Unknxxxx";
      END;
      name[12] := hex[tNum MOD 16]; tNum := tNum DIV 16;
      name[11] := hex[tNum MOD 16]; tNum := tNum DIV 16;
      name[10] := hex[tNum MOD 16]; tNum := tNum DIV 16;
      name[ 9] := hex[tNum MOD 16]; 
      EnterString(name, tHsh);
      INC(count);
      RETURN tHsh;
    END newAnonBkt;

    PROCEDURE ptrTargetName(ptr : IdDesc) : HashBucketType;
      VAR ix  : CARDINAL;
          hsh : HashBucketType;
          str : ARRAY [0 .. 79] OF CHAR;
    BEGIN
      ix := 0;
      GetSourceRep(ptr^.name, str, ix);
      GetSourceRep(ptrBkt, str, ix);
      EnterString(str, hsh);
      RETURN hsh;
    END ptrTargetName;

  END AnonHandler;

(* ----------------------------------------------------- *)

    PROCEDURE GetDesignator(VAR des : DesigRec);
      VAR stt  : DStateType;
	  tmp  : ExprDesc;
	  base : IdDesc;		(* the entire object *)
	  pMod : IdDesc;		(* the parent module *)
	  hash : HashBucketType;
    BEGIN
     (*
      *     TyDesig -> desigSy Designator Type .
      *  Designator -> (ident [dot ident] | fixNum) {Selector} endSy .
      *    Selector -> ident | upArrow | lBrac TyExpr .
      *
      *  -- we must bind the designator "on the fly, here"
      *  -- first token must be either a fixNum, or ident
      *)
      IF symSmbl = fixNum THEN 
	CreateIdDesc(anonBkt,base,posParNode);
	base^.posIndex := lexAtt.fixValue;
	base^.parType  := NIL;
	GetSymSmbl;			(* read past fixNm *)
      ELSE
        hash := lexAtt.hashIx; 		(* save the hashId *)
	GetSymSmbl;			(* read past ident *)
	IF symSmbl = dot THEN
	  LookupInModList(hash,pMod);
	  GetSymSmbl;			(* read past dot   *)
	  hash := lexAtt.hashIx;
	  GetSymSmbl;			(* read past ident *)
	ELSE
	  pMod := thisMod;
	END;
	LookupInThisScope(pMod^.scope,hash,base);
	Assert(base <> NIL, "PRECON VARIABLE NOT FOUND");
	MakeLinkerName(base);
      END;
      des.variable := base;
      SelectListBegin(des, stt);
      LOOP
	CASE symSmbl OF
	| ident   : PushIdentifier(stt,lexAtt.hashIx);	GetSymSmbl;
	| upArrow : PushDereference(stt);		GetSymSmbl;
	| lBrac   : GetSymSmbl; GetExp(tmp); PushSubscript(stt,tmp);
	| endSy   : GetSymSmbl; EXIT;
	END;
      END;
      SelectListEnd(stt);
    END GetDesignator;

    PROCEDURE GetFuncCall(exp : ExprDesc);
      VAR par : ExprDesc;
    BEGIN
     (*
      *   TyFnCall -> fnDesSy FuncCall Type .
      *   FuncCall -> Designator lPar {TyExpr} rPar .
      *)
      GetDesignator(exp^.name);
      GetSymSmbl; (* lPar *)
      WHILE symSmbl <> rPar DO
	GetExp(par); LinkRight(exp^.paramSeq,par);
      END;
      GetSymSmbl; (* rPar *)
    END GetFuncCall;

    PROCEDURE GetRanges(exp : ExprDesc);
      VAR lOp,rOp : ExprDesc;
    BEGIN
      InitSequence(exp^.rangeSeq);
      GetSymSmbl; (* lCurly *)
      WHILE symSmbl <> rCurly DO
	GetExp(lOp); 
	IF symSmbl = nilSy THEN rOp := NIL; GetSymSmbl ELSE GetExp(rOp) END;
	LinkRight(exp^.rangeSeq,MakeRangeDesc(lOp,rOp));
      END;
      GetSymSmbl; (* rCurly *)
    END GetRanges;

    PROCEDURE GetExp(VAR exp : ExprDesc);
      VAR class : ExprNodeClass;
	  idPtr : IdDesc;
	  state : DStateType;
    BEGIN
      IF symSmbl = constSy THEN
       (*
	*   TyLiteral -> Constant. -- as for any other sym-file constant
	*)
	ConDef(idPtr);
	CreateExprDesc(exp,literalNode);
	exp^.conValue := idPtr^.conValue;
	exp^.exprType := idPtr^.conType;
      ELSE (* not a literal *)
	(* $R- *)
	class := VAL(ExprNodeClass,ORD(symSmbl));
	(* $R= *)
	GetSymSmbl;
       (*
	*    TyDesig -> desigSy Designator Type .
	*   TyFnCall -> fnDesSy FuncCall Type .
	*    TyBinop -> opClass TyExpr TyExpr Type.
	*     TyUnop -> opClass TyExpr Type.
	*)
	CreateExprDesc(exp,class);
	IF class <= negateNode THEN
	  GetExp(exp^.leftOp);
	  IF class <= inNode THEN GetExp(exp^.rightOp) END;
        ELSE
	  CASE class OF
	  | desigNode       : GetDesignator(exp^.name);
	  | constructorNode, 
	    setDesigNode    : GetRanges(exp);
	  | adrDesigNode    : Assert(FALSE);
	  | funcDesigNode   : GetFuncCall(exp);
	  END;
	END;
	Type(exp^.exprType);
      END;
    END GetExp;

    PROCEDURE ParsePreconExpr(mod : IdDesc;
			  VAR exp : SYSTEM.ADDRESS);
      VAR tmp : ExprDesc;
    BEGIN
      thisMod := mod;
     (*
      *   PreconExp -> preconSy TyExpr .
      *      TyExpr -> TyDesig | TyFnCall | TyLiteral | TyBinop | TyUnop .
      *)
      GetSymSmbl;
      GetExp(tmp);
      exp := tmp;
    END ParsePreconExpr;

(* ----------------------------------------------------- *)
       (*$S-*)
       PROCEDURE Check(expected : TerminalSymbols);
       BEGIN
         IF symSmbl <> expected THEN 
           SymbolMessage(expected,symSmbl);
	   Assert(FALSE);
         END;
       END Check;
       (*$S=*)

    PROCEDURE CopyEnums(VAR id : IdDesc;
			    sq : Sequence);
      VAR curs   : ElemPtr;
	  objPtr : IdDesc;
	  done   : BOOLEAN;
    BEGIN
      InitCursor(sq,curs);
      SuspendList();
      WHILE NOT Ended(curs) DO
	GetNext(curs,objPtr);
	InsertRef(id^.scope,objPtr,done);
	IF NOT done THEN ErrIdent(265,objPtr^.name) END;
      END;
      ResumeList();
    END CopyEnums;

    (*****************************************************)
     VAR lastType  : TypeDesc;
         aliasMods : IdTree;
     VAR thisMod   : IdDesc; (* desc. of current symfile *)
	 bindSeq   : Sequence;(* of TypeDescs to bind    *)
    (*****************************************************)

    PROCEDURE BindFields(seq : Sequence);
      VAR curs : ElemPtr;
	  elem : TypeDesc;
    BEGIN
      InitCursor(seq,curs);
      WHILE NOT Ended(curs) DO
        GetNext(curs,elem);
        BindFieldOffsets(elem^);
      END;
    END BindFields;

    PROCEDURE HeaderCheck();
    BEGIN (* Header = VersionNumber DefModName. *)
      IF  (minVersion <= lexAtt.fixValue) AND
	  (lexAtt.fixValue <= symVersion) THEN
        GetSymSmbl; (* read past fixNum *)
      ELSE 
  	StdError.WriteString("Bad version number ... got value ");
  	StdError.WriteCard(lexAtt.fixValue,0); StdError.WriteLn;
  	StdError.WriteString("Should have been in [");
  	StdError.WriteCard(minVersion,0); StdError.WriteString(" .. ");
  	StdError.WriteCard(symVersion,0); StdError.WriteLn;
  	AbortMessage(' Sorry');
      END;
(*
 *)
      IF thisMod^.name <> lexAtt.hashIx THEN
        ErrIdent(301,lexAtt.hashIx); (* wrong mod name *)
      END;
(**)  Check(ident); GetSymSmbl; (* read past ident *)
    END HeaderCheck;

    PROCEDURE Marker(VAR modId : IdDesc);
    BEGIN
      IF symSmbl = dot THEN modId := thisMod;
      ELSIF symSmbl = slash THEN modId := pervasiveUnit;
      ELSE
(**)    Check(ident);
        LookupInModList(lexAtt.hashIx,modId);
(**)    Assert(modId <> NIL);
        GetSymSmbl; (* ident *)
      END;
      GetSymSmbl; (* dot or slash *)
    END Marker; (* post : symSmbl = ident *)

    PROCEDURE QualIdent(VAR modId  : IdDesc;
                        VAR qualId : IdDesc;
                        VAR hshBkt : HashBucketType);
      VAR ptr : IdDesc;
    BEGIN (* QualIdent = Marker ident. *)
      Marker(modId);
      LookupInThisScope(modId^.exports,lexAtt.hashIx,qualId);
      hshBkt := lexAtt.hashIx;
      GetSymSmbl; (* ident *)
    END QualIdent;

    PROCEDURE FieldSeq(VAR fSeq : Sequence;  (* of IdDesc   *)
                       VAR fTre : IdTree;    (* visible ids *)
		       VAR mask : CHAR);     (* alignMask   *)
      VAR iPtr : IdDesc; ok : BOOLEAN;
          unTp, vTp : TypeDesc;
	  maxMask,		(* max align constraint *)
	  eMask, 		(* alignment of element *)
	  uMask : CHAR;		(* alignment of union   *)
    BEGIN
      maxMask := 0C;
      WHILE (symSmbl = ident) OR (symSmbl = nilSy) DO
        IF symSmbl = ident THEN (* ordinary field *)
          CreateIdDesc(lexAtt.hashIx,iPtr,fieldNode);
          GetSymSmbl;
          InsertRef(fTre,iPtr,ok);
          LinkRight(fSeq,iPtr);
          Type(iPtr^.fieldType);
	  IF iPtr^.fieldType^.alignMask > maxMask THEN (* !3 *)
	    maxMask := iPtr^.fieldType^.alignMask;
	  END;
        ELSE  (* create dummy IdDesc *)
          GetSymSmbl; (* get past nilSy *)
(**)      Check(caseSy); GetSymSmbl;
          CreateIdDesc(anonBkt,iPtr,fieldNode);
          LinkRight(fSeq,iPtr);
          CreateTypeDesc(thisMod,unTp,unions); uMask := 0C;
          iPtr^.fieldType := unTp;
          WHILE symSmbl = bar DO GetSymSmbl;
            CreateTypeDesc(thisMod,vTp,records);
            LinkRight(unTp^.fieldSeq,vTp);
            FieldSeq(vTp^.fieldSeq,fTre,eMask);
            (* variants fields go in sequence for this variant *)
            (* but go in identifier tree of the parent record. *)
	    IF eMask > uMask THEN uMask := eMask END; (* !3 *)
          END; (* while *)
	  unTp^.alignMask := uMask;
(**)      Check(endSy); GetSymSmbl;
(**)      Check(fixNum); (* and get type size *)
          unTp^.size := lexAtt.fixValue; GetSymSmbl;
	  IF uMask > maxMask THEN maxMask := uMask END; (* !3 *)
        END; (* if *)
      END; (* while *)
      mask := maxMask;
    END FieldSeq;

    PROCEDURE RecType(VAR recPtr : TypeDesc);
    (* RecordType  = recordSy { Fields } endSy.
       Fields      = ident Type | UnionType.
       UnionType   = caseSy {bar {Fields}} endSy.             *)
    BEGIN
      GetSymSmbl;
(*
 *  now moved to caller
 *
 *    CreateTypeDesc(thisMod,recPtr,records);
 *)
      FieldSeq(recPtr^.fieldSeq,recPtr^.fields,recPtr^.alignMask);
(*
 *    BindFieldOffsets(recPtr^);
 *)
(**)  Check(endSy); GetSymSmbl;
    END RecType;

    PROCEDURE ProcType(VAR tp : TypeDesc);
    (* ProcType = procedureSy lPar {Formal} rPar [colon Type] *)
      VAR fFm : FormalClass; 
	  fTp : TypeDesc;
	  fOd : CARDINAL;
    BEGIN
      GetSymSmbl;
(**)  Check(lPar); GetSymSmbl;
      WHILE symSmbl <> rPar DO (* seqOf FormalType *)
(**)    Check(charNum);
	fOd := 0;
        fFm := VAL(FormalClass,ORD(lexAtt.charValue));
        GetSymSmbl; 
       (*
	*  Multi-dimensional open arrays have a second
	*  charNum which specifies the dimensionality
	*)
	IF fFm >= openValForm THEN 
	  IF symSmbl = charNum THEN 
	    fOd := ORD(lexAtt.charValue);
	    GetSymSmbl;
	  ELSE 
	    fOd := 1;
	  END;
	END;
	Type(fTp);
        LinkRight(tp^.params,MakeFormal(fTp,anonBkt,anonBkt,fFm,fOd));
      END;
      GetSymSmbl;
      IF symSmbl = colon THEN GetSymSmbl;
        tp^.tyClass := funcTypes;
        Type(tp^.result);
      END;
      IF symSmbl = preconSy THEN ParsePreconExpr(thisMod,tp^.preCon) END;
    END ProcType;

    PROCEDURE WrappedTypeDesc(modDes : IdDesc;
                             VAR ptr : TypeDesc;
                                 tag : TyNodeClass);
    BEGIN
      CreateTypeDesc(modDes, ptr, tag); 
      ptr^.tyName := newAnonBkt(tag);
      ptr^.pubTag := anonPub;
    END WrappedTypeDesc;

    PROCEDURE MakeAndInsertTargetId(thisMod : IdDesc;
                                    targetT : TypeDesc);
      VAR idD : IdDesc;
          ok  : BOOLEAN;
    BEGIN
      CreateIdDesc(targetT^.tyName, idD, typeNode);
      idD^.typType := targetT;
      InsertRef(thisMod^.exports, idD, ok);
    END MakeAndInsertTargetId;

    PROCEDURE Type(VAR tpPtr : TypeDesc);
    (* Type = equals                  -- the last type
            | QualIdent               -- some known type
            | (plus QualIdent | nilSy) ActualType Size. 
                                      -- some new type   *)
      VAR iPtr, modId, realParent, enumConPtr, tpId : IdDesc;
          hsh : HashBucketType;
          count : CARDINAL;
          defOcc, ok : BOOLEAN;
    BEGIN
      IF symSmbl = equals THEN tpPtr := lastType; GetSymSmbl;
      ELSIF symSmbl IN SymbolSet{slash,ident,dot} THEN
        QualIdent(modId,tpId,hsh); (* modId not nec = thisMod *)
        tpPtr := tpId^.typType;
      ELSE (* actual type *)
        IF symSmbl = nilSy THEN
          iPtr := NIL; defOcc := FALSE; GetSymSmbl;
	  modId := thisMod;	(* line added, 13-Apr-91 fix *)
        ELSE (* maybe must insert now *)
(**)      Check(plus); GetSymSmbl;
          QualIdent(modId,iPtr,hsh);
          defOcc := iPtr = NIL;
          IF defOcc THEN (* this is the defining occurrence *)
            CreateIdDesc(hsh,iPtr,typeNode);
            InsertRef(modId^.exports,iPtr,ok);
          (* ----------------- *
	    StdError.WriteString("inserting ");
	    DiagName(hsh);
	    StdError.WriteCard(CARDINAL(iPtr),12);
	    StdError.WriteString(" in ");
	    DiagName(modId^.name);
	    IF ok THEN StdError.WriteString(" ok");
	    ELSE StdError.WriteString(" failed");
	    END;
	    StdError.WriteLn;
           * ----------------- *)
          END; (* symSmbl <> nilSy *)
        END; (* nilSy ==> anon type *)
        CASE symSmbl OF (* can this be avoided if already known? *)
        | lPar : GetSymSmbl; count := 0;
            WrappedTypeDesc(thisMod,tpPtr,enums); SuspendList();
	    (*
	     *  This code places the enumeration 
	     *  consts in the scope modId^.exports ...
	     *  this is not necessarily thisMod^.exports
	     *  so a separate insertion may be required
	     *)
            WHILE symSmbl = ident DO
              CreateIdDesc(lexAtt.hashIx,enumConPtr,constNode);
              WITH enumConPtr^ DO
                conType := tpPtr;
                conValue.fixValue := count;
              END;
              InsertRef(modId^.exports,enumConPtr,ok);
              LinkRight(tpPtr^.conSeq,enumConPtr);
              INC(count); GetSymSmbl;
            END;
            tpPtr^.cardinality := count; ResumeList();
(**)        Check(rPar); GetSymSmbl;
        | lBrac : GetSymSmbl;
            WrappedTypeDesc(thisMod,tpPtr,subranges);
(**)        Check(fixNum);
            tpPtr^.minRange := lexAtt.fixValue; GetSymSmbl;
(**)        Check(fixNum);
            tpPtr^.maxRange := lexAtt.fixValue; GetSymSmbl;
            Type(tpPtr^.hostType);
(**)        Check(rBrac); GetSymSmbl;
	    (*
		Assert: current symbol is type size, or error
	    *)
	    tpPtr^.alignMask := alignMap[lexAtt.fixValue]; (* !3 *)
        | arraySy : GetSymSmbl;
            WrappedTypeDesc(thisMod,tpPtr,arrays);

            IF defOcc THEN iPtr^.typType := tpPtr END;

            Type(tpPtr^.indexType);
(**)        Check(ofSy); GetSymSmbl;
            Type(tpPtr^.elementType);
	    tpPtr^.alignMask := tpPtr^.elementType^.alignMask; (* !3 *)
        | notEq : GetSymSmbl;
            WrappedTypeDesc(thisMod,tpPtr,hiddens);
        | setSy : GetSymSmbl;
            WrappedTypeDesc(thisMod,tpPtr,sets);
            Type(tpPtr^.baseType);
        | pointerSy : GetSymSmbl;
            WrappedTypeDesc(thisMod, tpPtr, pointers);
            (* Now, it is possible that this pointer may be  *)
            (* referenced before the declaration is complete *)
            (* e.g. in the case of a recursive structure ==> *)
            (* must make iPtr^.typType a valid reference.    *)
            IF defOcc THEN iPtr^.typType := tpPtr END;
            Type(tpPtr^.targetType);
            IF defOcc AND (tpPtr^.targetType^.pubTag = anonPub) THEN
              tpPtr^.targetType^.tyName := ptrTargetName(iPtr);
              MakeAndInsertTargetId(thisMod, tpPtr^.targetType);
            END;
        | stringSy : GetSymSmbl;
            WrappedTypeDesc(thisMod,tpPtr,stringTs);
            (* Now, it is possible that this pointer may be  *)
            (* referenced before the declaration is complete *)
            (* e.g. in the case of a recursive structure ==> *)
            (* must make iPtr^.typType a valid reference.    *)
            IF defOcc THEN iPtr^.typType := tpPtr END;
            Type(tpPtr^.targetType);
        | recordSy : 
	    WrappedTypeDesc(thisMod,tpPtr,records);
	    LinkRight(bindSeq,tpPtr);
            IF defOcc THEN iPtr^.typType := tpPtr END;
	    RecType(tpPtr);
        | procedureSy : 
	    WrappedTypeDesc(thisMod,tpPtr,procTypes);
            (* Again, it is possible that this type may be   *)
            (* forward referenced, so use same fixup ...     *)
            IF defOcc THEN iPtr^.typType := tpPtr END;
	    ProcType(tpPtr);
        ELSE AbortMessage('bad type begin symbol in SYM');
        END;
(**)    Check(fixNum); (* and get type size *)
        tpPtr^.size := lexAtt.fixValue; GetSymSmbl;
        (* now get qualified type name *)
        IF defOcc THEN

	  IF modId^.name = thisCompileUnit^.name THEN
	    realParent := thisCompileUnit;
	  ELSE realParent := modId;
	  END;

          iPtr^.typType := tpPtr;
          tpPtr^.parentMod := realParent;
          tpPtr^.tyName := iPtr^.name;
          tpPtr^.pubTag    := namedPub;
        ELSIF iPtr <> NIL THEN 
          tpPtr := iPtr^.typType;
        END;
      END;
      lastType := tpPtr;
    END Type;

    PROCEDURE ConDef(VAR idd : IdDesc);
    (* ConDef = constSy ident Value .
       Value  = fixNum CharNum [Type] | charNum | floatNum 
              | charLit | litstring | bigSetCon Type 
	      | heapConst Type | nilSy. *)
      VAR iPtr : IdDesc; tPtr : TypeDesc;
          dummy : BOOLEAN; class : TyNodeClass;
    BEGIN
      GetSymSmbl; (* discard constSy *)
      CreateIdDesc(lexAtt.hashIx,iPtr,constNode);
      idd := iPtr;
      GetSymSmbl; (* discard ident *)
      WITH iPtr^ DO
        CASE symSmbl OF
        | fixNum : (* stow value *)
            conValue.fixValue := lexAtt.fixValue; GetSymSmbl;
(**)        Check(charNum); (* value is tyClass of const *)
            class := VAL(TyNodeClass,ORD(lexAtt.charValue));
            GetSymSmbl;
            IF (class = enums) OR (class = subranges) THEN Type(tPtr);
            ELSE tPtr := PointerTo(class);
            END;
        | charNum :
            conValue.charValue := lexAtt.charValue;
            tPtr := PointerTo(chars);
            GetSymSmbl;
        | floatNum :
            conValue.floatValue := lexAtt.floatValue;
            tPtr := PointerTo(RR);
            GetSymSmbl;
        | litstring :
(*! may be best just to copy lexAtt, provided strHigh is set for "" *)
            conValue.stringIx := lexAtt.stringIx;
            conValue.strHigh := lexAtt.strHigh;
            tPtr := PointerTo(SS);
            GetSymSmbl;
        | charLit :
            conValue.stringIx := lexAtt.stringIx;
            conValue.charValue := lexAtt.charValue;
            IF conValue.charValue = "" THEN
              conValue.strHigh := 0;
            ELSE conValue.strHigh := 1;
            END;
            tPtr := PointerTo(S1);
            GetSymSmbl;
        | bigSetCon : (* stow value and set typeDesc ptr... *)
            conValue.patternIx := lexAtt.patternIx;
            GetSymSmbl;
            Type(tPtr);
	| heapConst :
	    conValue.adrsValue := lexAtt.adrsValue;
	    GetSymSmbl; (* read past heapConst symbol *)
            Type(tPtr);
        | nilSy :
            conValue.adrsValue := nilValue;
            GetSymSmbl;
            tPtr := PointerTo(adrs);
        ELSE AbortMessage('bad const declaration');
        END; (* case *)
        conType := tPtr;
      END; (* with *)
      InsertRef(thisMod^.exports,iPtr,dummy);
    END ConDef;

    PROCEDURE TypeDef(); (* ownSym not needed *)
    (* TypeDef = typeSy ident Type. *)
      VAR tpId : IdDesc;
          tpTp : TypeDesc;
          dummy : BOOLEAN;
          hash : HashBucketType;
    (* 
     *  in almost all cases, the call of Type() causes
     *  the insertion of the IdDesc in the scope -- thus
     *  a new Id desc need only be formed for the exceptions.
     *  The exception arises when the type is a synonym for
     *  a type which is already known. In this case an IdRec 
     *  already exists, but a new one must be formed for the 
     *  synonym which is currently being parsed ...    
     *)
    BEGIN
      GetSymSmbl;
(**)  Check(ident);
      hash := lexAtt.hashIx; GetSymSmbl;
      Type(tpTp);
      LookupInThisScope(thisMod^.exports,hash,tpId);
      IF tpId = NIL THEN (* exceptional case *)
        IF (tpTp <> NIL) AND
	   (tpTp^.parentMod <> NIL) THEN
	  LookupInThisScope(tpTp^.parentMod^.exports,hash,tpId);
          IF tpId = NIL THEN CreateIdDesc(hash,tpId,typeNode) END;
          InsertRef(thisMod^.exports,tpId,dummy);
          (* ----------------- *
	    StdError.WriteString("exceptional insert ");
	    DiagName(hash);
	    StdError.WriteCard(CARDINAL(tpId),12);
	    StdError.WriteString(" in ");
	    DiagName(thisMod^.name);
	    IF dummy THEN StdError.WriteString(" ok");
	    ELSE StdError.WriteString(" failed");
	    END;
	    StdError.WriteLn;
            * ----------------- *)
	(*
	 *  this next fixes a bug with the qualified importation
	 *  of enumeration types which are synonyms for other
	 *  types.			(kjg) April 90
	 *)
          tpId^.typType := tpTp;
	  IF (tpTp^.tyClass = enums) THEN
	    CopyEnums(thisMod,tpTp^.conSeq);
	  END;
        END;
(*
ELSE
    StdError.WriteString("already inserted ");
    DiagName(hash);
    StdError.WriteCard(CARDINAL(tpId),12);
    StdError.WriteString(" in ");
    DiagName(thisMod^.name);
    StdError.WriteLn;
 *)
      END;
       (*
	*  Beware of assuming that any old opaque from 
	*  a module's own sym file is necessarily an 
	*  "own opaque" -- it might be an alias from the 
	*  definition module. Line here + 3 fixes. (kjg 13-Jul-90)
	*
	*  Remember -- hiddens are other module's opaques
	*  opaqueTemps are this module's opaques which will be
	*  elaborated in due course. 
	*)
      IF   (tpTp^.tyClass = hiddens) AND
	   (tpTp^.parentMod = thisCompileUnit) THEN
        tpTp^.pubTag  := opaqueAlias; (* default was hiddens    *)
        tpTp^.tyClass := opaqueTemp;  (* default was hiddens    *)
	tpTp^.resolvedType := NIL;
        LinkRight(unitImports,tpId); (* for implemented? check *)
      END;
    END TypeDef;

    PROCEDURE VarDef(cls : FormalClass);
    (*  VarDef = varSy ident Type. *)
      VAR iPtr : IdDesc; dummy : BOOLEAN;
    BEGIN
      GetSymSmbl;
(**)  Check(ident);
      CreateIdDesc(lexAtt.hashIx,iPtr,varNode);
      GetSymSmbl;
     (* ========================================================= *)
     (* ====== optional aliases in interface symbol files ======= *)
     (* ========================================================= *)
      IF symSmbl = litstring THEN
        iPtr^.varOffset := lexAtt.stringIx;
        GetSymSmbl;
      ELSE iPtr^.varOffset := 0;
      END;
     (* ========================================================= *)
      WITH iPtr^ DO
        varClass := cls;
        Type(varType);
        origMod := thisMod;
      END;
      InsertRef(thisMod^.exports,iPtr,dummy);
    END VarDef;

    PROCEDURE GetProcDef(own : BOOLEAN;
		     VAR pId : IdDesc);
    (*  ProcDef = procedureSy ident Type. *)
      VAR clss : IdNodeClass;
    BEGIN
      IF own THEN clss := procHeader ELSE clss := externProc END;
      GetSymSmbl; (* procedureSy *)
(**)  Check(ident);
      CreateIdDesc(lexAtt.hashIx,pId,clss);
      GetSymSmbl;
     (* ========================================================= *)
     (* ====== optional aliases in interface symbol files ======= *)
     (* ========================================================= *)
      IF symSmbl = litstring THEN
        pId^.extAlias := lexAtt.stringIx;
        GetSymSmbl;
      ELSE pId^.extAlias := 0;
      END;
     (* ========================================================= *)
      Type(pId^.procType);
    END GetProcDef;

    PROCEDURE ProcDef(own : BOOLEAN);
      VAR iPtr : IdDesc; ok : BOOLEAN;
    BEGIN
      GetProcDef(own,iPtr);
      InsertRef(thisMod^.exports,iPtr,ok);
      IF own THEN (* add to elaborate list *)
        IF ok THEN LinkRight(unitImports,iPtr) END;
        iPtr^.uphill := thisMod;
	iPtr^.frame  := iPtr; (* procedures define their own frame *)
      ELSE (* is an extern proc *)
	iPtr^.module   := thisMod;
	iPtr^.frame    := NIL;
	iPtr^.nonLeaky := thisMod^.library; (* ==> no ind. rec. *)
      END;
    END ProcDef;

    PROCEDURE ConProc();
    (* ConProc = upArrow ident ActualProc.              *)
    (* ActualProc = charNum charNum -- standard procs   *)
    (*            | Marker ProcDef [bar].               *)
    (* Marker  = slash | dot | ident dot.               *)
      VAR iPtr  : IdDesc;
	  pPtr  : IdDesc;
          modId : IdDesc;
	  own, ok : BOOLEAN;
    BEGIN
      GetSymSmbl; (* upArrow *)
      CreateIdDesc(lexAtt.hashIx,iPtr,conProc);
      InsertRef(thisMod^.exports,iPtr,ok);
      GetSymSmbl; (* ident *)
      IF symSmbl = charNum THEN (* stFunc or stProc *)
        iPtr^.idClass := VAL(IdNodeClass,ORD(lexAtt.charValue));
        GetSymSmbl; (* charNum *)
        iPtr^.procVal := VAL(StandardProcs,ORD(lexAtt.charValue));
        GetSymSmbl; (* charNum *)
      ELSE
        Marker(modId);
	Assert(modId <> NIL);
	InsertRef(aliasMods,modId,ok);
	own := (modId = thisCompileUnit); 
	(* 
	 * own ==> actual proc. is from this compilation unit
	 *)
	GetProcDef(own,pPtr);
        InsertRef(modId^.exports,pPtr,ok); 
        IF NOT ok THEN (* fix for problem with id already present *)
          LookupInThisScope(modId^.exports,pPtr^.name,pPtr);
        END;
	(* 
	 *  this proc. could be present already or might be added
	 *  when the symbol file is loaded. In the case of own mods,
	 *  it is always the successful insert which adds the proc
	 *  to the unitImports list for the elaboration check.
	 *)
        WITH pPtr^ DO
	  IF own THEN
	    IF ok THEN LinkRight(unitImports,pPtr) END;
            uphill := thisMod;
	    frame  := pPtr; (* procedures define their own frame *)
          ELSE (* is an extern proc *)
	    module   := modId;
	    frame    := NIL;
          END;
	END;
        iPtr^.procId := pPtr;
        (*
         *  the reason for this bar symbol is that a non-leaky
         *  procedure may be referenced through an alias in a
         *  module which does not load the original module,
         *  and hence would not know that the proc was safe
         *)
        IF symSmbl = bar THEN
          IF NOT own THEN pPtr^.nonLeaky := TRUE END;
          GetSymSmbl; (* bar *)
        END;
      END;
    END ConProc;

    PROCEDURE Definitions(own : BOOLEAN);
    (* Definition = { (ConDef | TypeDef | ProcDef | VarDef) }. *)
      VAR cls  : FormalClass; 
	  void : IdDesc;
    BEGIN
      InitAnons();
      IF own THEN cls := export ELSE cls := extern END;
      LOOP
        CASE symSmbl OF
        | constSy : ConDef(void);
        | typeSy  : TypeDef();  (* own not needed *)
        | varSy   : VarDef(cls);
        | procedureSy : ProcDef(own);
        | upArrow : ConProc();
        | endSy   : EXIT;
        ELSE AbortMessage('bad SYM definition')
        END;
      END;
    END Definitions;

    PROCEDURE ParseSymbolFile(modPtr : IdDesc);
    (* --------------------------------------------------------	*
     *   Unit = Header [ Kind ] ModuleImports SymbolModule 	*
     *  		          ImportObjects keySy eofSy .	*
     *   Header        = VersionNumber ident.			*
     *   Kind          = (nilSy | bar | fromSy) [upArrow] .	*
     *   ModuleImports = lBrac {ident keySy} rBrac .		*
     *   SymbolModule  = moduleSy { Definition } endSy .	*
     *   ImportObjects = importSy { Definition } endSy .	*
     * --------------------------------------------------------	*
     *  Note that the ImportObjects are written out only for 	*
     *  types but that they are simply skipped when reading.	1*
     *  This reflects a semantic change, and could be removed.	*
     *  However it provides some additional key checking safety.*
     * --------------------------------------------------------	*)

      VAR own : BOOLEAN;        (* currently importing own syms *)
          hsh : HashBucketType;
          ptr : IdDesc;         (* a temporary pointer in loop  *)
	  fOk : BOOLEAN;

    BEGIN (* ParseSymbolFile *)
      PshSymScanState;
      own := (modPtr = thisCompileUnit);
      thisMod := modPtr; 
      HeaderCheck();
      IF (symSmbl = nilSy) AND NOT own THEN
	(*
	 *  this next marks the exportNodes of system modules
         *  so as to ensure that they are not named in ref files 
	 *)
        modPtr^.system := TRUE;
        modPtr^.libSpx := 0; 
	(*
	 *  and externProcs of !LIBRARY (nonRec) modules so that 
         *  they are not presumed to engage in indirect recursion 
	 *)
        modPtr^.library := TRUE; 
	GetSymSmbl;
      ELSIF symSmbl = bar THEN
        GetSymSmbl;
        IF own THEN INCL(modState,nonRec);
        ELSE modPtr^.library := TRUE;
        END;
      ELSIF symSmbl = fromSy THEN (* !FOREIGN (macro) module *)
        GetSymSmbl;
        IF NOT own THEN
	  modPtr^.macro   := TRUE;
	  modPtr^.library := TRUE;
        ELSE AbortMessage('How is this a .mod when .def was FOREIGN?');
        END;
	IF symSmbl = litstring THEN
	  modPtr^.libSpx := lexAtt.stringIx;
	  GetSymSmbl;
        ELSE modPtr^.libSpx  := 0; 
	END;
	(*
	 *  and now test if it is also !INTERFACE FOR_C!
	 *)
	IF symSmbl = forSy THEN
	  GetSymSmbl;
	  IF NOT own THEN
	    modPtr^.direct := TRUE;
	  END;
	  RelaxLexicalRules();
	END;
      END;
      IF symSmbl = upArrow THEN (* is .RETCUT *)
	IF own THEN INCL(modState,retCutAll);
	ELSE modPtr^.retCut := TRUE;
	END;
        GetSymSmbl;
      END;
      Check(lBrac); GetSymSmbl;
       (*
	*  the symbol file header is parsed. We must
	*  now read the module import list of this symfile
	*)
      WHILE symSmbl = ident DO
        hsh := lexAtt.hashIx;
(*
IF hsh = thisCompileUnit^.name THEN
StdError.WriteString("Indirect import of self in: ");
DiagName(modPtr^.name);
StdError.WriteLn;
END;
 *)
        GetSymSmbl; (* read past ident *)
        LookupInModList(hsh,ptr);
        IF ptr = NIL THEN
          CreateIdDesc(hsh,ptr,exportNode);
          LinkRight(globalModList,ptr);
          ptr^.keyValue := lexAtt.keyValue;

	  IF verbose IN modState THEN 
	    StdError.WriteString("Recursing to new file");
	    StdError.WriteLn;
	  END;
          OpenOldSymFile(hsh,fOk);
          IF fOk THEN
            ParseSymbolFile(ptr);
          ELSE SetFlagOn(filErrors);
          END;
	  CloseOldSymFile();
	  thisMod := modPtr; 

        ELSE (* already known *)
          IF ptr^.keyValue <> lexAtt.keyValue THEN
            ErrIdent(300,hsh);
          END;
        END;
	IF superVerbose IN modState THEN 
          ListKey(hsh,lexAtt.keyValue);
	END;
(**)    Check(keySy); GetSymSmbl; (* past keySy *)
      END; (* while *)
(**)  Check(rBrac);    GetSymSmbl;
(**)  Check(moduleSy); GetSymSmbl;
      Definitions(own);
(**)  Check(endSy);    GetSymSmbl;
      IF own THEN
(**)    Check(importSy); GetSymSmbl;
        WHILE symSmbl < keySy DO GetSymSmbl END; (* also stops on eofSy *)
        symKeyValue := lexAtt.keyValue;
        (*
         *  own module imports have been inserted into 
         *  the global scope, now put into a dummy entry
         *  in the global module list ...
         *)
        CreateIdDesc(modPtr^.name,ptr,exportNode);
        ptr^.exports := thisCompileUnit^.scope;
        LinkRight(globalModList,ptr);
        ptr^.keyValue := lexAtt.keyValue;
        ptr^.loaded := TRUE;
      ELSE
        WHILE symSmbl < keySy DO GetSymSmbl END; (* also stops on eofSy *)
        modPtr^.keyValue := lexAtt.keyValue;
        modPtr^.loaded := TRUE;
      END;
      IF superVerbose IN modState THEN 
        ListKey(modPtr^.name,lexAtt.keyValue);
      END;
(**)  Check(keySy); GetSymSmbl;
(**)  Check(eofSy);
      IF verbose IN modState THEN 
        StdError.WriteString("Returning recursion");
        StdError.WriteLn;
      END;
      PopSymScanState;
    END ParseSymbolFile;

(*
 *  PROCEDURE ImportAliasModules();
 *
 *    PROCEDURE WalkTree(ptr : IdTree);
 *	VAR ok, dummy : BOOLEAN;
 *    BEGIN
 *	IF ptr <> NIL THEN
 *	  WalkTree(ptr^.left);
 *	  WalkTree(ptr^.right);
 *	  Assert(ptr^.ident^.loaded, "alias module not loaded");
 *	  IF NOT ptr^.ident^.loaded THEN
 *	    OpenOldSymFile(ptr^.ident^.name,ok);
 *	    IF ok THEN ParseSymbolFile(ptr^.ident);
 *	    ELSE SetFlagOn(filErrors);
 *	    END;
 *	    CloseOldSymFile();
 *	  END;
 *	END;
 *    END WalkTree;
 *
 *  BEGIN
 *    WalkTree(aliasMods);
 *)

    PROCEDURE BindAllFields();
    BEGIN
      BindFields(bindSeq);
      InitSequence(bindSeq);
    END BindAllFields;

    PROCEDURE CheckElaboration(seq : Sequence);
      VAR curs : ElemPtr; 
	  id   : IdDesc;
	  save : CARDINAL;
    BEGIN
      save := lastPos.line;
      lastPos.line := current^.body^.headerLine;
      InitCursor(seq,curs);
      WHILE NOT Ended(curs) DO
        GetNext(curs,id);
        WITH id^ DO
          IF (idClass = typeNode) AND
            (typType^.tyClass = opaqueTemp) AND
            (typType^.resolvedType = NIL) THEN 
	    ErrIdent(224,name);
          ELSIF (idClass = procHeader) AND (body = NIL) THEN
            ErrIdent(225,name);
          ELSIF (idClass = fwdHeader) AND (body = NIL) THEN
            ErrIdent(309,name);
	  ELSIF idClass IN IdClassSet{unknown,fwdMod} THEN
	    ErrIdent(322,name);
          END;
        END; (* with *)
      END;
      lastPos.line := save;
    END CheckElaboration;

BEGIN
  aliasMods := NIL;
  InitSequence(bindSeq);
END M2SymParser.

