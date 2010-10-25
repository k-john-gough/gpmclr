(****************************************************************)
(*                                                              *)
(*             Modula-2 Compiler Source Module                  *)
(*                                                              *)
(*                Parser and Tree Constructor.                  *)
(*                                                              *)
(*           (c) copyright 1987 SoftWare Automata.              *)
(*                                                              *)
(*      original module : kjg july 1987                         *)
(*      modifications   : fwd decs for ptrs to sbrngs 8-Mar-88  *)
(*                      : Expressions moved to sep. module      *)
(*                      : 17-Apr. exp. lists for nested modules *)
(*                      : 23-April convert pars to open arrays  *)
(*                      : 29-June fix error in TypeDec()        *)
(*                      : 17-July include nilSy in firstExp     *)
(*                      : 16-Aug fix bug in opaque type elab.   *)
(*                      : 31-Aug improve error 203 reporting    *)
(*	1989		: 12-Feb-89 fix DoImports, new err 280  *)
(*                      : 14-Feb jrh variant label range checks *)
(*                      : 26-Feb kjg fix halt set in for stmnt  *)
(*                      : 04-Mar kjg fix error 116 in Array     *)
(*                      : 09-Mar kjg correct fix of 16-Aug-88   *)
(*			: 11-Mar kjg backpatch formal opaques   *)
(*			: 13-Mar kjg better syntactic recovery  *)
(*			: 17-Mar kjg fix funcs returning opaque *)
(*			:  7-Apr kjg proctypes now in TypePatch *)
(*			: 21-Apr kjg recognize !MACRO pragma    *)
(*			: 10-May kjg Wirthian export semantics  *)
(*                      : 15-May jrh size and alignment         *)
(*			: 25-May kjg empty unions deleted	*)
(*			: 27-May kjg illegal uplevel refs	*)
(*			: 20-Jun jrh split Errors 204/205  	*)
(*			: 11-Aug kjg implement forward procs    *)
(*			: 03-Oct jrh subrange bad size fix      *)
(*			: 03-Oct jrh array size limit checks    *)
(*			: 08-Nov kjg uses BindFieldOffsets	*)
(*	1990		: 29-Mar kjg fix multiple 206 errors    *)
(*			: 30-Mar kjg 16-bit subranges now ok	*)
(*			:  2-Apr kjg  8-bit subranges now ok	*)
(*			:  2-Apr kjg fix of error in GetParams  *)
(*		        :  5-Apr kjg set tyPt = NIL in Type     *)
(*		        : 11-Apr kjg fix error in TypePatch     *)
(*			: 11-Apr kjg reference RelaxLexical...  *)
(*			:  3-Jul kjg semi errMsg in formal list *) 
(*			: 28-Aug kjg fix array of bad subrange  *)
(*			:  4-Sep kjg fix div by size=0 error	*)
(*			:  8-Sep kjg use M2Machin alignMap	*)
(*                      : 19-Sep kjg excl fwdHdrs from unitExps *)
(*                      : 13-Dec kjg export on top of fwdHdr ok *)
(*	1991		: 14-Aug kjg fix up anonTypes in VarDec *)
(*	1992		: 24-Feb kjg fix align of open actuals  *)
(*			: 12-Apr jrh forward import		*)
(*			: 11-May jrh error on dupl elaboration	*)
(*			: 14-May jrh fix fwd import for proc/ptr*)
(*								*)
(*   =============== merged mips and i386 source ============	*)
(*			   kjg 22 Mar 93			*)
(*                                                              *)
(*      2003            :        kjg compute "pubTag" attribute *)
(*                                   for CLR version.           *)
(*                                                              *)
(****************************************************************
$Log: m2parser.mod,v $
Revision 1.9  1997/04/03 03:29:58  hynd
In ForStatement if cv not found test from error 204 then 239

Revision 1.8  1997/01/16 04:46:52  gough
        changes for preconditions.  Procedure types can now have preconditions
        as can constant procedures.  MoveParamsToScope is all new.

Revision 1.7  1996/11/27 02:35:48  lederman 
add parsing for EXCEPT and FINALLY clauses

Revision 1.6  1996/07/30 00:01:05  gough
parse STRING OF <type> construct

Revision 1.5  1996/06/24 04:58:04  gough
when declaring a procedure implementation with no param list check that
not only is the definition param list empty (as before), but that the
return type is also NIL.

Revision 1.4  1995/03/23 23:01:55  gough
parse multidimensional open arrays in parameter lists

# Revision 1.3  1994/12/01  00:28:42  lederman
# add endIdLineNumber
#
# Revision 1.2  1994/07/01  05:19:48  lederman
# extend subrange size calc. to include 4-byte on 64-bit target
#
# Revision 1.1  1994/04/07  05:10:41  lederman
# Initial revision
#
*****************************************************************
Revision 1.8  94/03/29  17:07:25  gough
fix up diagnosis for interfaces with alias names _and_ double declarations

Revision 1.7  93/11/16  08:58:27  gough
allow for multiple context sensitive marks in DEFs

Revision 1.6  93/09/30  15:32:02  gough
use safer algorithm for finding the line with PROCEDURE on it

Revision 1.5  93/09/30  10:26:47  gough
change linenumber semantics to use headerLine in StrucRec record

Revision 1.4  93/07/08  17:07:00  gough
Changes to VarDef, ConstDev and TypeDef to allow empty declarations
in conformity with the standard. (bug reported by Yan, at UQ)
*****************************************************************)

IMPLEMENTATION MODULE M2Parser;

  IMPORT SYSTEM;
  IMPORT StdError;
  FROM Types IMPORT Int8, Card8, Int16, Card16, Int32, Card32;

  FROM M2NodeDefs  IMPORT 
	IdDesc, IdRec, IdTree, IdNodeClass, IdClassSet, CreateIdDesc, 
	InsertRef, InsertAndCheck, PubEnum,
	TypeDesc, TyNodeClass, CreateTypeDesc, StandardProcs,
	FormalType, FormalClass, FormalRec, MakeFormal,
	globalModList, thisCompileUnit, pervasiveUnit, current,
	StartImportList, StartExportList, unitImports,
	StrucTree, StrucRec, TyClassSet, TypeRec,
	SuspendList, ResumeList, modState;

  FROM M2StructureDefs IMPORT CreateStrucTree, 
	StatDesc, StatNodeClass, StatRec, CreateStatDesc,
	CreateConditional, IfDesc, IfRec, 
	CaseStatDesc, CaseStatRec, CaseDesc, CaseRec, CreateCaseDesc;

  FROM M2Designators IMPORT
	DesigRec, ExprDesc, WithDesc, WithRec, ParseDesignator;

  FROM M2Alphabets IMPORT TerminalSymbols, SymbolSet, Spellix,
			HashBucketType, Flags, FlagSet, errors,
			LexAttType, ModStateFlags, ModStateSet;

  FROM M2Scanner   IMPORT symbol, lexAtt, GetSymbol, InitScanner, 
			RelaxLexicalRules,
			SetFlagOn, CurrentFlags;

  FROM M2NameHandler IMPORT Commit, anonBkt, sysBkt, libBkt, 
			SpellingIndex, retCutBkt, ExcludeExt,
			directBkt, foreignBkt, nonRecBkt;

  FROM M2InOut     IMPORT OpenInput, DiagName, ErrIdent, Error, lastPos;

  FROM GenSequenceSupport IMPORT Sequence, ElemPtr, LinkLeft,
			LinkRight, InitCursor, GetNext,
			InitSequence, NextIsLast, Ended,
			DisposeList;

  FROM M2SSUtilities IMPORT 
			Lookup, LookupInThisScope, LookupInModList,
			OrdinalValue, Compatible, EnterScope, ExitScope,
			MinOfOrdType, MaxOfOrdType, IsOrdinalType, 
			IsOwnOpaque, EquivPrecons,
			IndexCardinality, Align, AlignAndAdd,
			BindFieldOffsets, MaxSizeAndAlignment;

  FROM M2TabInitialize IMPORT PointerTo, ExclStrExt;

  FROM M2SymParser IMPORT CheckElaboration;

  FROM M2Traversal IMPORT TraversePrecon;

  FROM M2MachineConstants IMPORT bitsInWord, bytesInWord, cardMax, exceptOK,
			     nilValue, maxSetCard, charMax, intMax, adrSize,
			     alignMap, sizeLimit, largeArray;

  FROM M2CompOperations IMPORT OrdRelOp;

  FROM M2ExpParser IMPORT ConstExpr, Qualident, QualRest,
			PreCondition,
			SkipTo, ErrSkip, ImportOwnSyms, CompImports,
			ActualParams, Expression, GetCaseRange, Error203;

  FROM ProgArgs  IMPORT Assert;

(***************************************************************)

    VAR unitName : HashBucketType;
	opaqFrms : Sequence;
	fwdGlobs : Sequence; 

  CONST followDefs   = SymbolSet{ varSy, endSy, constSy,
				typeSy, procedureSy, eofSy};
	followDecs   = followDefs + SymbolSet{beginSy, moduleSy };
	followImport = followDecs + 
		       SymbolSet{importSy, exportSy, fromSy };
        firstExp     = SymbolSet{plus, minus, notSy, lPar, ident, nilSy,
			litstring, fixNum, charLit, charNum, floatNum};
	firstType    = SymbolSet{lPar, lBrac, ident, arraySy, stringSy,
			recordSy, setSy, pointerSy, procedureSy};
	firstStat    = SymbolSet{ident, caseSy, ifSy, whileSy, repeatSy,
			loopSy, forSy, withSy, exitSy, returnSy, retrySy};

	idSet    = SymbolSet{ident};
	semiSet  = SymbolSet{semi};
	commaSet = SymbolSet{comma};
	exitSet  = semiSet + followImport;


  (******************************************************)
    PROCEDURE Error205Or323(idClass : IdNodeClass);
    BEGIN
      IF idClass = unknown THEN
	Error(323); (* use in decl before decl *)
      ELSE
	Error(205); (* not a type name *)
      END;
    END Error205Or323;

    PROCEDURE ErrSkip205Or323(haltSet : SymbolSet; idClass : IdNodeClass);
    BEGIN
      IF idClass = unknown THEN
	ErrSkip(haltSet,323);
      ELSE
	ErrSkip(haltSet,205);
      END;
    END ErrSkip205Or323;

    PROCEDURE ErrIdent205Or323(name : HashBucketType; idClass : IdNodeClass);
    BEGIN
      IF idClass = unknown THEN
	ErrIdent(323,name);
      ELSE
	ErrIdent(205,name);
      END;
    END ErrIdent205Or323;

  (******************************************************)
(*
 *   PROCEDURE IsObjectArray(type : TypeDesc) : BOOLEAN;
 *   BEGIN
 *     RETURN (type^.tyClass = arrays) OR
 *            ((type^.tyClass = sets) AND (type^.size > bytesInWord))
 *   END IsObjectArray;
 *)
(*
 *  diagnostic ---
 *
 *  PROCEDURE TypeQualId(ty : TypeDesc);
 *  BEGIN
 *    DiagName(ty^.parentMod^.name);
 *    StdError.Write(".");
 *    DiagName(ty^.tyName);
 *  END TypeQualId;
 *)

  (******************************************************)

    PROCEDURE BackPatch(seq : Sequence);
     (*
      * back-patches target types of pointers,
      * and the formals and results of procTypes 
      *)
      VAR curs, fCrs : ElemPtr;
	  pType : TypeDesc;
	  idPtr : IdDesc;
	  frml  : FormalType;
     BEGIN
      InitCursor(seq,curs);
      WHILE NOT Ended(curs) DO
	GetNext(curs,pType); (* assert: pType <> NIL *)
	WITH pType^ DO
	(*
	 * there are two separate cases here:
	 *  . pointer types with unresolved targets
	 *  . procedure types with formals and return
	 *    types unresolved
	 *)
	  IF (tyClass = pointers) OR
	     (tyClass = stringTs) THEN
	    Lookup(forwardHsh,idPtr);
	    IF idPtr <> NIL THEN (* is it a type *)
	      IF idPtr^.idClass <> typeNode THEN
		ErrIdent205Or323(forwardHsh,idPtr^.idClass);
		targetType := NIL;
	      ELSE targetType := idPtr^.typType;
	      END;
	    ELSE ErrIdent(211,forwardHsh);
	    END;
	  ELSE (* procType: do formals first *)
	    InitCursor(params,fCrs);
	    WHILE NOT Ended(fCrs) DO
	      GetNext(fCrs,frml);
	      IF frml^.type = NIL THEN (* unresolved *)
		Lookup(frml^.tNam,idPtr);
		IF idPtr <> NIL THEN (* is it a type *)
	          IF idPtr^.idClass <> typeNode THEN
		    ErrIdent205Or323(frml^.tNam,idPtr^.idClass);
	          ELSE frml^.type := idPtr^.typType;
	          END;
	        ELSE ErrIdent(211,frml^.tNam);
	        END;
	      END;
	    END; (* while, now do result type, noting    *)
		 (* that forward result types are tagged *)
		 (* with the "impossible" tyClass II     *)
	    IF (result <> NIL) AND (result^.tyClass = II) THEN
	      Lookup(result^.tyName,idPtr);
	      IF idPtr <> NIL THEN (* is it a type *)
	        IF idPtr^.idClass <> typeNode THEN
		  ErrIdent205Or323(result^.tyName,idPtr^.idClass);
	        ELSE result := idPtr^.typType;
	        END;
	      ELSE ErrIdent(211,result^.tyName);
	      END;
	    END; (* of result patch *)
	    IF preCon <> NIL THEN 
	      CreateIdDesc(anonBkt,idPtr,unknown);
	      idPtr^.procType := pType;
	      idPtr^.scope    := NIL;
	      EnterScope(idPtr);
	      MoveParamsToScope(idPtr);
	      TraversePrecon(pType);	(* bind precon expr *)
	      ExitScope;
	    END;
	  END;
	END; (* with *)
      END; (* while *)
    END BackPatch;

    PROCEDURE ResolveFormals();
      VAR curs : ElemPtr; frm : FormalType;
    BEGIN
      InitCursor(opaqFrms,curs);
      WHILE NOT Ended(curs) DO
        GetNext(curs,frm);
        Assert(frm^.type^.tyClass = opaqueTemp);
        frm^.type := frm^.type^.resolvedType;
      END;
    END ResolveFormals;
        
    PROCEDURE Subrange(halt : SymbolSet; VAR ty : TypeDesc);
    (* Subrange = [ident] lBrac ConstExpr dotDot ConstExpr rBrac.*)
    (* not nested since it is called from TypePatch also *)
      VAR elemType, cType : TypeDesc;
	  val : LexAttType;
	  new, exp : SymbolSet;
	  badLimit : BOOLEAN;
    BEGIN (* assert: symbol = lBrac *)
      GetSymbol; elemType := ty; (* save IN value *)
      CreateTypeDesc(thisCompileUnit,ty,subranges);
      new := halt + SymbolSet{dotDot,rBrac};
      badLimit := FALSE;
      ConstExpr(new,cType,val);
      IF elemType = NIL THEN elemType := cType;
      ELSIF NOT Compatible(elemType,cType) THEN
	Error(207); elemType := NIL;
      END;
      IF cType<>NIL THEN
        ty^.minRange := OrdinalValue(cType,val);
      ELSE
	badLimit := TRUE;
      END;
      IF symbol = dotDot THEN GetSymbol;
      ELSE
	exp := halt + firstExp;
	ErrSkip(exp,112);
      END;
      new := halt + SymbolSet{rBrac};
      ConstExpr(new,cType,val);
      IF NOT Compatible(elemType,cType) THEN
	Error(207); elemType := NIL;
      END;
      IF cType<>NIL THEN
        ty^.maxRange := OrdinalValue(cType,val);
      ELSE
	badLimit := TRUE;
      END;
      (* now clean up some nasty semantic details *)
      IF elemType <> NIL THEN
	ty^.alignMask := elemType^.alignMask;
	IF elemType^.tyClass = subranges THEN
	  elemType := elemType^.hostType;
	ELSIF elemType = PointerTo(S1) THEN
	  elemType := PointerTo(chars);
	END;
	IF OrdRelOp(greater,elemType,ty^.minRange,ty^.maxRange) THEN
	  Error(209); badLimit := TRUE; elemType := NIL;
	ELSE (* this will need modification if smaller sizes 
		are allocated to shorter subranges *)
	  ty^.size := elemType^.size;
	END;
      END; (* must test again, elemType could have been set to NIL *)
      IF (elemType <> NIL) AND (elemType^.tyClass <= UU) THEN
	IF elemType^.tyClass = II THEN elemType := PointerTo(ints);
	ELSE elemType := PointerTo(cards);
	END;
      END;
      IF badLimit OR (elemType=NIL) THEN (* avoid further bad range errors *)
	ty^.minRange := 0;
	ty^.maxRange := 0;
      END;
      ty^.hostType := elemType;
      IF elemType = PointerTo(cards) THEN
	IF ty^.maxRange <= MAX(Card8) THEN 
	  ty^.size := 1;
	ELSIF ty^.maxRange <= MAX(Card16) THEN
	  ty^.size := 2;
	ELSIF ty^.maxRange <= MAX(Card32) THEN
	  ty^.size := 4;
	END;
        ty^.alignMask := alignMap[ty^.size];
      ELSIF elemType = PointerTo(ints) THEN
	IF (ty^.maxRange <= MAX(Int8)) AND
            (SYSTEM.CAST(INTEGER,ty^.minRange) >= MIN(Int8)) THEN
          ty^.size := 1;
	ELSIF (ty^.maxRange <= MAX(Int16)) AND
           (SYSTEM.CAST(INTEGER,ty^.minRange) >= MIN(Int16)) THEN
          ty^.size := 2;
	ELSIF (ty^.maxRange <= MAX(Int32)) AND
           (SYSTEM.CAST(INTEGER,ty^.minRange) >= MIN(Int32)) THEN
          ty^.size := 4;
	END;
        ty^.alignMask := alignMap[ty^.size];
      END;
      IF symbol = rBrac THEN GetSymbol;
      ELSE 
        ErrSkip(halt,115); elemType := NIL;
      END;
      IF elemType = NIL THEN ty := NIL END; (* fix of bug 28-Aug-90 *)
    END Subrange;

    PROCEDURE Type(halt : SymbolSet;
	       VAR tyPt : TypeDesc);
    (* Type = SimpleType | ArrayType | RecordType 
	    | UnionType | SetType | PointerType | ProcType .*)
    (* SimpleType = Qualident | Enumeration | Subrange .    *)

      VAR id : IdDesc; ixTy, elTy : TypeDesc; new : SymbolSet;

      PROCEDURE Enumeration(VAR ty : TypeDesc);
	CONST restart = SymbolSet{ident,comma,rPar};
	VAR   id    : IdDesc; 
	      count : CARDINAL;
	      new   : SymbolSet; 
	      ok    : BOOLEAN;
      BEGIN (* Enumeration = lPar { ident } rPar . *)
	new := restart + halt;
	CreateTypeDesc(thisCompileUnit,ty,enums); GetSymbol;
	count := 0;
	SuspendList(); (* don't list enum consts *)
	LOOP
	  IF symbol = ident THEN
	    CreateIdDesc(lexAtt.hashIx,id,constNode);
	    WITH id^ DO
	      conType := ty;
	      conValue.fixValue := count;
	      InsertAndCheck(current^,id,ok);
	      IF NOT ok THEN Error(265) END;
	    END;
	    LinkRight(ty^.conSeq,id);
	    GetSymbol; INC(count);
	  ELSE ErrSkip(new,108);
	  END;
	  IF (symbol =rPar) OR (symbol IN halt) THEN EXIT;
	  ELSIF symbol = comma THEN GetSymbol;
	  ELSE ErrSkip(new,110);
	  END;
	END; (* loop *)
	IF count > 255 THEN Error(231) END;
	ty^.cardinality := count;
	ResumeList();
	IF symbol = rPar THEN GetSymbol;
	ELSE Error(111);
	END;
      END Enumeration;

      PROCEDURE Array(VAR ty : TypeDesc);
	VAR new : SymbolSet;

      PROCEDURE RecArray (VAR ty : TypeDesc);
       (* Handle recursive array declarations due to
	* "ARRAY indextype,indextype OF ..." syntax;
	* indirect recursion via Type handles the
	* "ARRAY indextype OF ARRAY indextype OF ..." syntax
        *)
      VAR ixTy : TypeDesc;
      BEGIN
	CreateTypeDesc(thisCompileUnit,ty,arrays); GetSymbol;
	WITH ty^ DO
	  Type(new,indexType);
	  IF (indexType <> NIL) AND NOT (indexType^.tyClass IN 
	      TyClassSet{enums,chars,subranges,bools}) THEN
	    Error(206); indexType := NIL; (* not ordinal type *)
	  END;
	  IF (symbol <> comma) AND (symbol <> ofSy) THEN ErrSkip(new,116) END;
	  IF symbol = comma THEN
	    (* Recursively process nested array *)
	    RecArray(elementType);
	  ELSIF symbol = ofSy THEN
	    (* Process ultimate element type *)
	    GetSymbol;
	    Type(halt,elementType);
	  END;
	  (* Array size is multiple of size of element type *)
	  IF (elementType<>NIL) AND 
	     (indexType<>NIL) THEN
	    (*
	     *  this next guards against valid declarations of
	     *  arrays of records of zero size causing div0 traps
	     *)
	    IF  (elementType^.size <> 0) AND
	        (IndexCardinality(ty) > (sizeLimit DIV elementType^.size))
	      THEN Error(310);
	    ELSE
	      size := elementType^.size * IndexCardinality(ty);
	      IF size > largeArray THEN Error(496); END;
	      alignMask := elementType^.alignMask;
	    END;
	  END;
	END (* WITH ty^ *) ;
      END RecArray;

      BEGIN (* ArrayType = arraySy {SimpleType} ofSy Type .*)
	new := halt + SymbolSet{ofSy,comma};
	RecArray (ty);
      END Array;
 
      PROCEDURE Set(VAR ty : TypeDesc);
	VAR   bsTy : TypeDesc; new : SymbolSet;
      BEGIN (* SetType = setSy ofSy SimpleType. *)
	CreateTypeDesc(thisCompileUnit,ty,sets);
	new := halt + SymbolSet{ofSy};
	GetSymbol; SkipTo(new,116);
	IF symbol = ofSy THEN GetSymbol END;
	Type(halt,bsTy);
        ty^.size := bytesInWord;
	IF bsTy <> NIL THEN
	  WITH bsTy^ DO
            (* assume maxSetCard < MAX(INTEGER) so
               that unsigned comparisons are ok below *)
	    IF IsOrdinalType(bsTy) THEN (* new mar-90 *)
              IF (MinOfOrdType(bsTy) >= maxSetCard) OR
                 (MaxOfOrdType(bsTy) >= maxSetCard) THEN
	        Error(210); bsTy := NIL;
	      ELSE 
	        INC(ty^.size, (* cardinality = maxRange + 1 *)
	      		MaxOfOrdType(bsTy) DIV bitsInWord * bytesInWord);
	      END;
	    ELSE Error(206); bsTy := NIL;
	    END;
	  END; (* with *)
	END; (* if not NIL *)
	ty^.baseType := bsTy;
      END Set;

      PROCEDURE Pointer(VAR ty : TypeDesc);
	VAR new : SymbolSet;
      BEGIN
	CreateTypeDesc(thisCompileUnit,ty,pointers);
	GetSymbol; (* read past pointerSy *)
	IF symbol = toSy THEN GetSymbol;
	ELSE
	  new := firstType + halt;
	  ErrSkip(new,132);
	END;
	Type(halt,ty^.targetType);
      END Pointer;

      PROCEDURE String(VAR ty : TypeDesc);
	VAR new : SymbolSet;
      BEGIN
	(* "STRING" "OF" Type *)
	CreateTypeDesc(thisCompileUnit,ty,stringTs);
	GetSymbol; (* read past stringSy *)
	IF symbol = ofSy THEN GetSymbol;
	ELSE
	  new := firstType + halt;
	  ErrSkip(new,132);
	END;
	Type(halt,ty^.targetType);
      END String;

      PROCEDURE Variant(hlt : SymbolSet;
			tTp : TypeDesc; (* tag type *)
		     mn, mx : CARDINAL; (* tag rnge *)
		    VAR vTp : TypeDesc; (* var flds *)
		    VAR tre : IdTree);  (* fieldIds *)
      (*
       * process one variant of a union;
       *       caseLabelSequence colonSy fieldListSequence
       *)
	VAR lo, hi : CARDINAL; val : LexAttType;
	    first, last : SymbolSet; cTp : TypeDesc;
      BEGIN
	last := hlt + SymbolSet{colon,comma};
	first := hlt + SymbolSet{dotDot,colon,comma};
	LOOP
	  ConstExpr(first,cTp,val);
	  IF Compatible(tTp,cTp) THEN
	    lo := OrdinalValue(cTp,val);
	    IF OrdRelOp(greater,tTp,mn,lo) OR OrdRelOp(less,tTp,mx,lo) THEN
	      Error(215); lo := mn;
	    END;
	  ELSE Error(207); lo := mn;
	  END;
	  IF symbol = dotDot THEN GetSymbol;
	    ConstExpr(last,cTp,val);
	    IF Compatible(tTp,cTp) THEN
	      hi := OrdinalValue(cTp,val);
	      IF OrdRelOp(greater,tTp,mn,hi) OR OrdRelOp(less,tTp,mx,hi) THEN
		Error(215); hi := mx;
	      END;
	    ELSE Error(207); hi := mx;
	    END;
	    IF OrdRelOp(less,tTp,hi,lo) THEN Error(209); hi := lo END;
	  END;
	  IF symbol = comma THEN GetSymbol;
	  ELSIF symbol IN last THEN EXIT;
	  ELSE SkipTo(last,110);
	  END;
	END; (* loop *)
	IF symbol = colon THEN
	  GetSymbol;
	  FieldListSeq(hlt,vTp,tre);
	ELSE ErrSkip(hlt,117);
	END;
      END Variant;

      PROCEDURE Union(ext  : SymbolSet;
		  VAR fSeq : Sequence;
		  VAR fTre : IdTree;
		  VAR tagSize, unionSize : CARDINAL;
		  VAR tagAlignment, unionAlignment : CHAR);
	VAR new, res : SymbolSet;
	    iPtr, tpId : IdDesc;
	    hsh : HashBucketType;
	    tgTp, unTp, vTp : TypeDesc;
	    min, max : CARDINAL;
	    haveColon, haveTagField, ok : BOOLEAN;
      BEGIN (* symbol = caseSy *)
	GetSymbol; iPtr := NIL; haveColon := FALSE;
	new := ext + SymbolSet{ofSy,bar,elseSy,endSy};

	res := new + firstExp;
	IF symbol = ident THEN hsh := lexAtt.hashIx;
	  GetSymbol; CreateIdDesc(hsh,iPtr,fieldNode); 
	END;
	IF symbol = colon THEN 
	  haveColon := TRUE; GetSymbol;
	  IF iPtr <> NIL THEN (* ident was tag field *)
	    InsertRef(fTre,iPtr,ok); LinkRight(fSeq,iPtr);
	    IF NOT ok THEN Error(222) END;
	  END;
	END;
	IF symbol = ident THEN (* second ident *)
	  IF NOT haveColon THEN Error(117); END;
	  hsh := lexAtt.hashIx;
	  GetSymbol; QualRest(hsh,tpId);
	ELSIF (NOT haveColon) AND (iPtr <> NIL) THEN (* only one ident *)
	  Error(501); iPtr := NIL; QualRest(hsh,tpId);
	ELSE (* nothing, just colon, or ident colon *)
	  ErrSkip(new,108); tpId := NIL;
	END;
	haveTagField := iPtr<>NIL; (* evaluate here to allow for old syntax *)
	tagSize := 0; tagAlignment := 0C;
	IF (tpId <> NIL) AND (tpId^.idClass = typeNode) AND
	    IsOrdinalType(tpId^.typType) THEN
	  tgTp := tpId^.typType;
	  IF haveTagField THEN
	    iPtr^.fieldType := tgTp;
	    tagSize := tgTp^.size; tagAlignment := tgTp^.alignMask;
	  END;
	  min := MinOfOrdType(tgTp);
	  max := MaxOfOrdType(tgTp);
	ELSE tgTp := NIL; min := 0; max := cardMax; Error(206);
	END;
	CreateIdDesc(anonBkt,iPtr,fieldNode); (* dummy field *)
	CreateTypeDesc(thisCompileUnit,unTp,unions);
	iPtr^.fieldType := unTp;
	EXCL(new,ofSy);
	IF symbol = ofSy THEN GetSymbol ELSE ErrSkip(new,116) END;
	LOOP
	  IF symbol IN firstExp THEN
	    CreateTypeDesc(thisCompileUnit,vTp,records);
	    LinkRight(unTp^.varSeq,vTp);
	    Variant(new,tgTp,min,max,vTp,fTre);
	    MaxSizeAndAlignment(unTp,vTp); 
	  END;
	  IF symbol = bar THEN GetSymbol;
	  ELSIF symbol IN new THEN EXIT;
	  ELSE ErrSkip(res,123);
	  END;
	END;
	IF symbol = elseSy THEN GetSymbol;
	  CreateTypeDesc(thisCompileUnit,vTp,records);
	  LinkRight(unTp^.varSeq,vTp);
	  FieldListSeq(new,vTp,fTre);
	  MaxSizeAndAlignment(unTp,vTp);
	END;
	IF symbol = endSy THEN GetSymbol;
	ELSE ErrSkip(ext,103);
	END;
	unionSize := unTp^.size;
	unionAlignment := unTp^.alignMask;
	(*
	   don't link empty unions into sequence
	*)
	IF unionSize <> 0 THEN LinkRight(fSeq,iPtr) END;
      END Union;

      PROCEDURE IdFieldList(ext  : SymbolSet;
			VAR fSeq : Sequence;
			VAR fTre : IdTree;
			VAR size : CARDINAL;
			VAR alignment : CHAR);
	VAR new : SymbolSet; idSeq : Sequence;
	    iPtr : IdDesc; ty : TypeDesc;
	    ok : BOOLEAN; curs : ElemPtr;
	    numFields : CARDINAL;
      BEGIN (* symbol = ident *)
	InitSequence(idSeq);
	numFields := 0;
	size := 0; alignment := 0C;
	new := ext + SymbolSet{ident,colon};
	REPEAT (* assert: sy = ident *)
	  CreateIdDesc(lexAtt.hashIx,iPtr,fieldNode);
	  InsertRef(fTre,iPtr,ok);
	  IF ok THEN
	    LinkRight(idSeq,iPtr); LinkRight(fSeq,iPtr);
	  ELSE Error(222);
	  END;
	  GetSymbol; (* get past id *)
	  IF symbol = comma THEN GetSymbol;
	  ELSIF symbol <> colon THEN ErrSkip(new,117);
	  END;
	UNTIL symbol <> ident;
	IF symbol <> colon THEN ErrSkip(ext,117);
	ELSE GetSymbol;
	  Type(ext,ty);
	  InitCursor(idSeq,curs);
	  WHILE NOT Ended(curs) DO
	    GetNext(curs,iPtr); iPtr^.fieldType := ty;
	    INC(numFields);
	  END;
	  IF ty<>NIL THEN
	    (* Same calculation as for array *)
	    size := ty^.size * numFields;
	    alignment := ty^.alignMask;
	  END;
	END; (* sy = colon *)
	DisposeList(idSeq);
      END IdFieldList;

      PROCEDURE FieldListSeq(hlt  : SymbolSet;
			 VAR rTy : TypeDesc;
			 VAR fTre : IdTree);
	VAR res : SymbolSet;
	    tagSize, IDFLOrUnionSize : CARDINAL;
	    tagAlign, IDFLOrUnionAlign : CHAR;
      BEGIN
	res := hlt + SymbolSet{ident,caseSy,semi};
	LOOP
	  IF symbol IN SymbolSet{ident,caseSy} THEN
	    IF symbol = ident THEN
	      IdFieldList(hlt,rTy^.fieldSeq,fTre,
			  IDFLOrUnionSize,IDFLOrUnionAlign);
	    ELSE (* symbol = caseSy *)
	      Union(hlt,rTy^.fieldSeq,fTre,
		    tagSize,IDFLOrUnionSize,tagAlign,IDFLOrUnionAlign);
	      (* Internal alignment, for tagfield if any *)
	      AlignAndAdd(rTy,tagAlign,tagSize);
	    END;
	    (* Now internal alignment for the field list or union *)
	    AlignAndAdd(rTy,IDFLOrUnionAlign,IDFLOrUnionSize);
	  END (* symbol in {ident,caseSy} *) ;
	  IF symbol = semi THEN GetSymbol;
	  ELSIF symbol IN hlt THEN EXIT;
	  ELSE ErrSkip(res,105);
	  END;
	END (* LOOP *) ;
	(* Now ensure that the entire record finishes on an alignment
	   boundary, as required by HP-C. *)
	WITH rTy^ DO size := Align(size,alignMask); END;
      END FieldListSeq;

      PROCEDURE RecordType(VAR ty : TypeDesc);
	VAR new   : SymbolSet;
	    flags : FlagSet;
      BEGIN (* assert : symbol = recordSy *)
	GetSymbol; CreateTypeDesc(thisCompileUnit,ty,records);
	ty^.size := 0; (* override default - record starts empty *)
	(* computing size requires machine specific knowledge regarding
	   (among other things) any alignment constraints              *)
	new := halt + SymbolSet{endSy};
	FieldListSeq(new,ty,ty^.fields);
	IF symbol = endSy THEN GetSymbol ELSE ErrSkip(halt,103) END;
	flags := CurrentFlags();
	IF flags * errors = FlagSet{} THEN BindFieldOffsets(ty^) END;
      END RecordType;

    BEGIN (* body of Type *)
      IF NOT(symbol IN firstType) THEN
        new := halt + firstType; ErrSkip(new,134);
        tyPt := NIL; (* (kjg) April 1990 *)
      END;
      CASE symbol OF
      | ident : 
	  new := halt + SymbolSet{lBrac}; 
	  Qualident(id);
	  IF id = NIL THEN ErrIdent(204,lexAtt.hashIx); tyPt := NIL;
	  ELSIF id^.idClass = typeNode THEN tyPt := id^.typType;
	  ELSE Error205Or323(id^.idClass); tyPt := NIL;
	  END;
	  IF symbol = lBrac THEN (* IN-ty is host type *)
	    IF NOT IsOrdinalType(tyPt) THEN  (* better diagnostics 28-Aug-90 *)
	      Error(206);
	      tyPt := NIL;
	    END;
	    Subrange(halt,tyPt); (* OUT-ty is constructed subrange type *)
	  END;
      | lPar      : Enumeration(tyPt);
      | lBrac     : tyPt := NIL; (* ==> no explicit host type *)
		    Subrange(halt,tyPt);
      | arraySy   : Array(tyPt);
      | setSy     : Set(tyPt);
      | stringSy  : String(tyPt);
      | pointerSy : Pointer(tyPt);
      | procedureSy : GetSymbol;
	  IF symbol <> lPar THEN tyPt := PointerTo(procTypes);
	  ELSE
	    CreateTypeDesc(thisCompileUnit,tyPt,procTypes);
	    ProcType(tyPt,FALSE); (* not forward *)
	  END;
      | recordSy : RecordType(tyPt);
      ELSE (* skip *)
      END;
    END Type;

    PROCEDURE ProcType (ty  : TypeDesc;
	 		fwd : BOOLEAN);
      CONST new = followDecs + SymbolSet{rPar} - SymbolSet{varSy};
	    end = followDecs + SymbolSet{semi,preconSy};
      VAR   res   : SymbolSet;
	    idPtr : IdDesc;
	    hshBk : HashBucketType;

      PROCEDURE GetFormal(hlt : SymbolSet;
			   fw : BOOLEAN;
		       VAR sq : Sequence);
	VAR tpId : IdDesc;
	    form : FormalClass;
	    hash : HashBucketType;
	    opnD : CARDINAL;
	    gotT : BOOLEAN;		(* already got type name *)
	    fmNm : HashBucketType;	(* optional formal name  *)
      BEGIN
       (*
	*  Do the lookahead to allow optional names here.
	*)
	IF symbol = ident THEN 
	  hash := lexAtt.hashIx; 
	  GetSymbol; 
	  IF symbol = colon THEN 
	    GetSymbol;
	    gotT := FALSE;
	    fmNm := hash;
	  ELSE 
	    fmNm := anonBkt;
	    gotT := TRUE;
	  END;
	ELSE
	  fmNm := anonBkt;
	  gotT := FALSE;
	END;
	form := valForm; (* x + binary 00 *)
	opnD := 0;
	IF symbol = varSy THEN
	  GetSymbol; INC(form,1); (* binary 01 *)
	END;
	IF symbol = arraySy THEN
	  GetSymbol; INC(form,2); (* binary 1x *)
	  opnD := 1;
	  IF symbol = ofSy THEN GetSymbol;
	  ELSE ErrSkip(hlt,116);
	  END;
	  WHILE symbol = arraySy DO
	    GetSymbol;
	    INC(opnD);
	    IF symbol = ofSy THEN GetSymbol;
	    ELSE ErrSkip(hlt,116);
	    END;
	  END;
	END;
	IF gotT OR (symbol = ident) THEN
	  IF NOT gotT THEN hash := lexAtt.hashIx; GetSymbol END;
	  IF NOT fw OR (symbol = dot) THEN (* 14-May-92 *)
	    QualRest(hash,tpId);
	    IF tpId = NIL THEN ErrSkip(hlt,204)
	    ELSIF tpId^.idClass = typeNode THEN
	      LinkRight(sq, MakeFormal(tpId^.typType,
                                       fmNm, tpId^.name, form, opnD));
	    ELSE
	      ErrSkip205Or323(hlt,tpId^.idClass);
	    END;
	  ELSE 
	    LinkRight(sq,MakeFormal(NIL,fmNm,hash,form,opnD)); 
	  END;
	ELSE ErrSkip(hlt,108);
	END;
	SkipTo(hlt,118); (* bad formal param *)
      END GetFormal;

    BEGIN (* assert : symbol = lPar *)
      GetSymbol;
      WITH ty^ DO
	IF symbol = rPar THEN GetSymbol;
	ELSE
	  res := new + SymbolSet{ident,varSy,arraySy,comma};
	  LOOP (* of formals *)
	    GetFormal(res,fwd,params);
	    IF symbol = comma THEN GetSymbol;
	    ELSIF symbol IN new THEN EXIT;
	    ELSE ErrSkip(res,110);
	    END;
	  END;
	  IF symbol = rPar THEN GetSymbol;
	  ELSE ErrSkip(followDecs,111);
	  END;
	END; (* if sy = rPar *)
	IF symbol = colon THEN
	  GetSymbol;
	  IF symbol = ident THEN
	    hshBk := lexAtt.hashIx; GetSymbol;
	    IF NOT fwd OR (symbol = dot) THEN (* 14-May-92 *)
	      QualRest(hshBk,idPtr);
	      IF idPtr = NIL THEN ErrSkip(end,204)
	      ELSIF idPtr^.idClass = typeNode THEN
	        result := idPtr^.typType;
	      ELSE
		ErrSkip205Or323(end,idPtr^.idClass);
		result := NIL;
	      END;
	    ELSE
	      (* II is a dummy, functions cannot return II *)
	      CreateTypeDesc(thisCompileUnit,result,II);
	      result^.tyName := hshBk;
	    END;
	    tyClass := funcTypes;
	  ELSE ErrSkip(end,108); (* not ident *)
	  END;
	ELSE SkipTo(end,117); (* no colon *)
	END; (* if colon *)
      END; (* with ty do *)
    END ProcType;

    (* Pointer type with possible forward reference  *)
    (* Procedure types with possible forward formals *)
    PROCEDURE TypePatch(halt : SymbolSet;
		      VAR ty : TypeDesc;
		      VAR sq : Sequence);
      VAR hsh : HashBucketType;
	  id  : IdDesc;
	  new : SymbolSet;
	  fwd : BOOLEAN;
	  old : TerminalSymbols;
    BEGIN
      old := symbol;
      GetSymbol;
      IF old = procedureSy THEN
	IF symbol <> lPar THEN ty := PointerTo(procTypes);
	ELSE (* a new procedure type ... *)
	  CreateTypeDesc(thisCompileUnit,ty,procTypes);
	  LinkRight(sq,ty);   (* put on backpatch list *)
	  ProcType(ty,TRUE); (* ==> allow fwd formals *)
	END;
      ELSE (* is pointerSy *)
	IF old = pointerSy THEN 
	  CreateTypeDesc(thisCompileUnit,ty,pointers);
	  IF symbol = toSy THEN GetSymbol ELSE ErrSkip(new,132) END;
	ELSE
	  CreateTypeDesc(thisCompileUnit,ty,stringTs);
	  IF symbol = ofSy THEN GetSymbol ELSE ErrSkip(new,132) END;
	END;
	new := firstType + halt;
	IF symbol = ident THEN (* possible forward reference *)
	  hsh := lexAtt.hashIx; GetSymbol; fwd := TRUE;
	  IF symbol = dot THEN (* qual.type ==> not forward! *)
	    QualRest(hsh,id); fwd := FALSE;
	  END;
	  IF (symbol = lBrac) AND fwd THEN (* simple subrange *)
	    Lookup(hsh,id); fwd := FALSE;
	  END;
	  IF NOT fwd THEN
	    IF id = NIL THEN ErrSkip(halt,204)
	    ELSIF id^.idClass = typeNode THEN
	      ty^.targetType := id^.typType;
	      IF symbol = lBrac THEN (* IN-ty is host type *)
	        Subrange(halt,ty^.targetType);
	      END; (* OUT-ty is new subrange *)
	    ELSE
	      ErrSkip205Or323(halt,id^.idClass);
	      ty^.targetType := NIL;
	    END;
	  ELSE ty^.forwardHsh := hsh; LinkRight(sq,ty);
	  END;
        ELSE Type(halt,ty^.targetType);
        END;
      END;
    END TypePatch;

    PROCEDURE TypeDec(halt : SymbolSet;
                   VAR seq : Sequence);
      VAR ptr, old, new : IdDesc;
          hsh : HashBucketType;
          ok  : BOOLEAN;
          actual : TypeDesc;
          tyStart, restart, typHalt : SymbolSet;

      PROCEDURE PropagateEnumConsts((*typNam : HashBucketType;*)
                                    oldId  : IdDesc; (* unknown class *)
                                    enumTp : TypeDesc);
       (*
	*  this procedure propagates enum constants
	*  outward (and then possibly inward) from a nested module scope
	*)

        VAR (*outScope, qual, exist : IdDesc;*)
	    targetCursor : ElemPtr;
            targetDesc : IdDesc;

        PROCEDURE CopyToTarget(VAR trg : IdRec);
	  VAR cPtr : ElemPtr; eCon : IdDesc;
	      exist : IdDesc;
        BEGIN
          InitCursor(enumTp^.conSeq,cPtr);
          WHILE NOT Ended(cPtr) DO
            GetNext(cPtr,eCon);
(*
 *	WriteString ("Insert "); DiagName (eCon^.name);
 *	WriteString (" into "); DiagName (trg.name); WriteLn;
 *)
            InsertAndCheck(trg,eCon,ok);
            IF NOT ok THEN ErrIdent(276,eCon^.name) END;
(*
 *	      LookupInThisScope(trg.scope,eCon^.name,exist);
 *	      IF exist <> eCon THEN ErrIdent(276,eCon^.name) END;
 *	    END;
 *)
          END;
	END CopyToTarget;

      BEGIN
        InitCursor(oldId^.fwdTargets,targetCursor);
        WHILE NOT Ended(targetCursor) DO
          GetNext(targetCursor,targetDesc);
	  CopyToTarget(targetDesc^);
	END;
      END PropagateEnumConsts;

      PROCEDURE MakeConstVisible(enumTp : TypeDesc);
       (*
	*  this procedure propagates enum constants
	*  of aliases into the current scope
	*)
	VAR cPtr : ElemPtr;
	    eCon : IdDesc;
	    exist : IdDesc;
      BEGIN
        InitCursor(enumTp^.conSeq,cPtr);
	SuspendList();
        WHILE NOT Ended(cPtr) DO
          GetNext(cPtr,eCon);
          InsertAndCheck(current^,eCon,ok);
          IF NOT ok THEN ErrIdent(276,eCon^.name) END;
        END; (* while *)
	ResumeList();
      END MakeConstVisible;

    BEGIN (* assert: symbol = typeSy *)
      GetSymbol;
      restart := halt + SymbolSet{ident,semi};
      typHalt := halt + semiSet;
      tyStart := typHalt + firstType;
      WHILE NOT (symbol IN halt) DO (* halt is ok *)
        IF symbol = ident THEN
          hsh := lexAtt.hashIx; GetSymbol;
          CreateIdDesc(hsh,ptr,typeNode);
          (* name is not inserted until AFTER type found (29:Jun:88) *)
          IF symbol = equals THEN 
            GetSymbol;
            IF (symbol = pointerSy) OR (symbol = procedureSy) THEN
	      TypePatch(typHalt,actual,seq);
            ELSE Type(typHalt,actual);
            END;
          ELSIF symbol = semi THEN
            IF defMod IN modState THEN
              CreateTypeDesc(thisCompileUnit,actual,opaqueTemp);
            ELSE
	      Error(223);
	      actual := NIL; (* 31-May-89 *)
            END;
          ELSE (* substitution error ? *)
            ErrSkip(tyStart,107);
            IF (symbol = pointerSy) OR (symbol = procedureSy) THEN
	      TypePatch(typHalt,actual,seq);
            ELSE Type(typHalt,actual);
            END;
          END;
          IF actual <> NIL THEN
	    IF actual^.size = 0 THEN Error(497) END;	(* no error? *)
	    IF actual^.tyName = anonBkt THEN actual^.tyName := hsh END;
          END;
          InsertAndCheck(current^,ptr,ok);
	  (*
	   *  ok ==> the new type name was not previously known
	   *  in this scope. However, the new type is an alias
	   *  for an enumeration then the enum constants need
	   *  to be made visible also
	   *)
	  IF actual = NIL THEN (* nothing *)
          ELSIF ok THEN 
	    ptr^.typType := actual;
	    IF  (actual^.tyClass = enums) AND
	        (actual^.parentMod <> thisCompileUnit) THEN
	      MakeConstVisible(actual);
	    END;
          ELSE (* could be: on export list; elab. of opaque type *)
            LookupInThisScope(current^.scope,hsh,old); (* ptr <> NIL *)
            IF old^.idClass = unknown THEN (* overwrite *)
		(* 
		 *  StdError.WriteString("old is ");
		 *  DiagName(old^.name);
		 *  StdError.WriteLn;
		 *)
              (* Need to propagate exported enum consts? *)
              IF actual^.tyClass = enums THEN
		(*
		 *  StdError.WriteString("is an enum");
		 *  StdError.WriteLn;
		 *)
                PropagateEnumConsts((*hsh,*)old,actual);
              END;
              old^ := ptr^; old^.typType := actual;
            ELSIF IsOwnOpaque(old) THEN
(*
 *    =====================================================
 *
 *        the "fix" of Aug-88 follows ...
 *        it has several residual problems which needed to be
 *        resolved by a generalised Compat. test and "resolvedType"

 *            IF (actual <> NIL) AND
 *               (actual^.tyClass IN TyClassSet{pointers,adrs}) THEN
 *              old^.typType^ := actual^; (* overwrite! 15-Aug-88 *)
 *     (* Old IdDesc is ok, but type is no longer opaque. The record *)
 *     (* may be pinned by a reference in a formal param list, while *)
 *     (* "actual" may now be pinned in the BackPatch list --- so... *)
 *     (* put the overwritten one on the list, and tag the old one   *)

 *        ... the pinned actual couldn't be removed from the list,
 *        so had to be tagged as "ignore", the new version went on
 *        the backpatch list so as to resolve the forward reference

 *              IF actual^.tyClass = pointers THEN
 *                LinkRight(seq,old^.typType); (* on backpatch list  *)
 *                actual^.tyClass := hiddens;  (* 'patch will ignore *)
 *              END;
 *
 *	============================================================
 *
 *      the new fix follows ... it does not copy structures
 *	instead it relies on all relevant code checking
 *
 *	... IF tyClass = opaqueTemp THEN ty := ty^.resolvedType ...
 *
 *	Note that an opaque cannot be elaborated as an opaque
 *	since in that case it it hard to guard against cycles
 *	of opaques. Hiddens (someone elses opaques) are ok
 *	string-types are also ok (Jul 1996).
 *
 *	============================================================
 *)
	      IF  (actual <> NIL) AND
		  (actual^.tyClass IN
			TyClassSet{hiddens,pointers,stringTs,adrs}) THEN
                IF old^.typType^.tyClass = opaqueTemp THEN
                  Assert(old^.typType^.pubTag = opaqueAlias);
                  actual^.pubTag := opaqueAlias;
                END;
                old^.typType^.resolvedType := actual;
                old^.typType := actual;
		(*
		 *  common code from here on
		 *)
              ELSE 
		Error(227);
                old^.typType^.resolvedType := PointerTo(adrs);
              END;
            ELSE Error203(old);
            END;
          END;
        ELSE ErrSkip(restart,108);
        END; (* assert: >= 1 sym consumed OR symbol in restart *)
        IF symbol = semi THEN 
	  GetSymbol;
          IF (symbol = preconSy) AND
	     (actual <> NIL) AND
	     ((actual^.tyClass = funcTypes) OR 
	      (actual^.tyClass = procTypes)) THEN
	    PreCondition(actual);
	  END;
        ELSE 
	  ErrSkip(restart,105); (* not sy in restart is ok *)
        END;
      END; (* semi or ident consumed next loop ==> all ok *)
    END TypeDec;

    PROCEDURE GetParams(hlt : SymbolSet;
		     VAR sq : Sequence);
      CONST max = 15;
            colRest = SymbolSet{arraySy,ident,semi,rPar};
      VAR   tpId : IdDesc; 
	    form : FormalClass;
            frm  : FormalType; 
	    patchQ : BOOLEAN;
	    openDs : CARDINAL;
	    count, ix : CARDINAL; res : SymbolSet;
	    hshArray : ARRAY [0..max] OF HashBucketType;
    BEGIN
      res := hlt + SymbolSet{comma,colon,ident,equals};
      form := valForm; (* binary 00 *)
      openDs := 0;
      IF symbol = varSy THEN
	GetSymbol; INC(form,1); (* binary 01 *)
      END;
      count := 0;
      LOOP
	IF symbol = ident THEN
	  IF count > max THEN Error(226); 
	  ELSE INC(count);
	  END;
	  hshArray[count - 1] := lexAtt.hashIx;
	  GetSymbol;
	ELSE ErrSkip(res,108);
	END;
	IF symbol = comma THEN GetSymbol;
	ELSIF symbol IN res THEN EXIT;
	ELSE ErrSkip(res,117);
	END;
      END;
      IF symbol = colon THEN GetSymbol;
      ELSE ErrSkip(colRest,117);
      END;
      IF symbol = arraySy THEN
	GetSymbol; INC(form,2); (* binary 1x *)
	openDs := 1;
	IF symbol = ofSy THEN GetSymbol;
	ELSE ErrSkip(res,116);
	END;
	WHILE symbol = arraySy DO
	  GetSymbol;
	  INC(openDs);
	  IF symbol = ofSy THEN GetSymbol;
	  ELSE ErrSkip(res,116);
	  END;
	END;
      END;
      IF symbol = ident THEN
	Qualident(tpId);
	IF tpId = NIL THEN ErrSkip(hlt,204)
	ELSIF (tpId^.idClass = typeNode) AND
	      (tpId^.typType <> NIL) THEN 	(* kjg 2-Apr-90 *)
          patchQ := tpId^.typType^.tyClass = opaqueTemp;
          IF patchQ AND (tpId^.typType^.resolvedType <> NIL) THEN
            tpId^.typType := tpId^.typType^.resolvedType; patchQ := FALSE;
          END;
	  FOR ix := 1 TO count DO
	    frm := MakeFormal(tpId^.typType,
                              hshArray[ix - 1],
                              tpId^.name, form, openDs);
	    LinkRight(sq,frm);
            IF patchQ THEN LinkLeft(opaqFrms,frm) END;
	  END;
	ELSE
	  ErrSkip205Or323(hlt,tpId^.idClass);
	END;
      ELSE ErrSkip(hlt,108);
      END;
      SkipTo(hlt,118); (* bad formal param *)
    END GetParams;

    PROCEDURE GetParamList(halt : SymbolSet; idPtr : IdDesc);
      VAR new,exit : SymbolSet;
    BEGIN
      WITH idPtr^ DO
	CreateTypeDesc(thisCompileUnit, procType, procTypes);
	IF symbol = lPar THEN (* else an empty param list *)
	  GetSymbol; (* lPar *)
	  IF symbol = rPar THEN GetSymbol;
	  ELSE
	    new := halt + SymbolSet{ident,rPar}; (* semi is in halt *)
	    exit := new - SymbolSet{ident,varSy};
	    LOOP (* of formals *)
	      GetParams(new, procType^.params);
	      IF symbol = semi THEN GetSymbol;
	      ELSIF symbol IN exit THEN EXIT;
	      ELSE ErrSkip(new,105); (* 3-jul fix *)
	      END;
	    END;
	    IF symbol = rPar THEN GetSymbol;
	    ELSE ErrSkip(followDecs,111);
	    END;
	  END; (* if sy = rPar *)
	  IF symbol = colon THEN
	    GetSymbol;
	    IF symbol = ident THEN
	      Qualident(idPtr);
	      IF idPtr = NIL THEN ErrSkip(halt,204) (* 12-Apr-92 *)
	      ELSIF idPtr^.idClass = typeNode THEN
		procType^.result := idPtr^.typType;
	      ELSE (* not type *)
		ErrSkip205Or323(halt,idPtr^.idClass); procType^.result := NIL;
	      END;
	      procType^.tyClass := funcTypes;
	    ELSE ErrSkip(halt,108); (* not ident *)
	    END;
	  ELSE SkipTo(halt,117); (* no colon *)
	  END; (* if colon *)
	END; (* of param list *)
      END; (* with *)
    END GetParamList;

    PROCEDURE CheckParams(hlt : SymbolSet;
		      VAR crs : ElemPtr);
      CONST max = 15;
            colRest = SymbolSet{arraySy,ident,semi,rPar};
      VAR   tpId  : IdDesc; 
	    pForm : FormalClass;
	    frm   : FormalType;
	    openD : CARDINAL;
	    count, ix : CARDINAL; res : SymbolSet;
	    hshArray : ARRAY [0..max] OF HashBucketType;
    BEGIN
      res := hlt + SymbolSet{comma,colon,ident,equals};
      pForm := valForm; (* binary 00 *)
      openD := 0;
      IF symbol = varSy THEN
	GetSymbol; INC(pForm,1); (* binary 01 *)
      END;
      count := 0;
      LOOP
	IF symbol = ident THEN
	  hshArray[count] := lexAtt.hashIx;
	  GetSymbol; INC(count);
	  IF count > max THEN Error(226); count := 0 END;
	ELSE ErrSkip(res,108);
	END;
	IF symbol = comma THEN GetSymbol;
	ELSIF symbol IN res THEN EXIT;
	ELSE ErrSkip(res,117);
	END;
      END;
      IF symbol = colon THEN GetSymbol;
      ELSE ErrSkip(colRest,117);
      END;
      IF symbol = arraySy THEN
	GetSymbol; INC(pForm,2); (* binary 1x *)
	openD := 1;
	IF symbol = ofSy THEN GetSymbol;
	ELSE ErrSkip(res,116);
	END;
	WHILE symbol = arraySy DO
	  GetSymbol;
	  INC(openD);
	  IF symbol = ofSy THEN GetSymbol;
	  ELSE ErrSkip(res,116);
	  END;
	END;
      END;
      IF symbol = ident THEN
	Qualident(tpId);
	IF tpId = NIL THEN ErrSkip(hlt,204)
	ELSIF tpId^.idClass = typeNode THEN
	  FOR ix := 0 TO count - 1 DO
	    IF Ended(crs) THEN Error(216);
	    ELSE
	      GetNext(crs,frm);
	      WITH frm^ DO
		fNam := hshArray[ix]; (* ignoring original name! *)
		IF type^.tyClass = opaqueTemp THEN
		  IF type^.resolvedType <> NIL THEN (* resolve *)
		    type := type^.resolvedType;
		  ELSE LinkLeft(opaqFrms,frm); (* and do later *)
		  END;
		END;
		IF (form <> pForm) OR 
		   (dimN <> openD) OR
		   (type <> tpId^.typType) THEN
		  ErrIdent(228,hshArray[ix]);
		END;
	      END; (* with *)
	    END;
	  END;
	ELSE ErrSkip205Or323(hlt,tpId^.idClass);
	END;
      ELSE ErrSkip(hlt,108);
      END;
      SkipTo(hlt,118); (* bad formal param *)
    END CheckParams;

    PROCEDURE CheckParamList(halt : SymbolSet; idPtr : IdDesc);
      VAR parCurs : ElemPtr;
      VAR new,exit : SymbolSet;
    BEGIN
      WITH idPtr^ DO
	InitCursor(procType^.params,parCurs);
	IF symbol <> lPar THEN
	  IF NOT Ended(parCurs) THEN Error(114) END;
	  IF procType^.result <> NIL THEN Error(228) END;
	ELSE
	  GetSymbol; (* get past lPar *)
	  IF symbol = rPar THEN (* empty param list *)
	    GetSymbol;
	    IF NOT Ended(parCurs) THEN Error(114) END;
	  ELSE
	    new := halt + SymbolSet{ident,rPar}; (* semi is in halt *)
	    exit := new - SymbolSet{ident,varSy};
	    LOOP (* of formals *)
	      CheckParams(new,parCurs);
	      IF symbol = semi THEN GetSymbol;
	      ELSIF symbol IN exit THEN EXIT;
	      ELSE ErrSkip(new,105); (* 3-jul fix *)
	      END;
	    END;
	    IF symbol = rPar THEN
	      GetSymbol;
	      IF NOT Ended(parCurs) THEN Error(114) END;
	    ELSE ErrSkip(followDecs,111);
	    END;
	  END; (* if sy = rPar *)
          (*
	   * now deal with function return types
	   *)
	  IF symbol = colon THEN
	    GetSymbol;
	    IF symbol <> ident THEN ErrSkip(halt,108);
	    ELSIF procType^.result = NIL THEN ErrSkip(halt,281);
	    ELSE (* is ok, so process it *)
	      Qualident(idPtr);
	      IF idPtr = NIL THEN ErrSkip(halt,204) (* 12-Apr-92 *)
	      ELSIF idPtr^.idClass <> typeNode THEN
		ErrSkip205Or323(halt,idPtr^.idClass);
	      ELSE (* check result type *)
		(*
		 * fix up opaques if possible
		 *)
                IF (procType^.result^.tyClass = opaqueTemp) AND
		   (procType^.result^.resolvedType <> NIL) THEN
                  procType^.result := procType^.result^.resolvedType;
		END;
		(*
		   now do the real check
		*)
		IF procType^.result <> idPtr^.typType THEN Error(229) END;
              END; (* else do check *)
	    END; (* else process it *)
	  ELSE (* no colon *)
	    SkipTo(halt,117);
	    IF procType^.result <> NIL THEN Error(228) END;
	  END; (*  no colon *)
	END; (* of param list *)
      END; (* with *)
    END CheckParamList;

    PROCEDURE ProcHeader(halt : SymbolSet;
                     VAR iPtr : IdDesc);
      VAR ok  : BOOLEAN; old : IdDesc; new : SymbolSet;
    BEGIN (* assert: symbol = procedureSy *)
      (* this procedure parses the procedure header. It also determines *)
      (* if the procedure is already declared, either as a result of a  *)
      (* forward declaration or a declaration in a definition module    *)
      INCL(halt,preconSy); new := halt; INCL(new,semi); 
      GetSymbol; 
      IF symbol = ident THEN
        CreateIdDesc(lexAtt.hashIx,iPtr,procNode);
	GetSymbol; (* read past ident *)
        iPtr^.uphill := current;
(*
 *  the following line must come _after_ iPtr
 *  has been fiddled with, otherwise native code
 *  versions find that iPtr^.frame is incorrectly
 *  pointing to the discarded original version (kjg Apr-90)
 *
 *	iPtr^.frame  := iPtr; (* procedures define their own frame *)
 *)
        InsertAndCheck(current^,iPtr,ok);
       (* ==================================================== *)
       (* ============ new code for alias names ============== *)
       (* ==================================================== *)
       (*         name --> ident[ "[" litstring "]" ].         *)
       (* ==================================================== *)
        IF symbol = lBrac THEN
          IF NOT (ModStateSet{defMod,directMod} <= modState) THEN
            Error(325);
          END;
          GetSymbol;
          IF symbol <> litstring THEN Error(141);
          ELSE
            iPtr^.extAlias := lexAtt.stringIx;
            GetSymbol;
          END;
          SkipTo(new + SymbolSet{rBrac},115);
          IF symbol = rBrac THEN GetSymbol END;
        ELSIF ModStateSet{defMod,directMod} <= modState THEN 
          iPtr^.extAlias := 0;
        END;
       (* ==================================================== *)
        IF ok THEN GetParamList(new,iPtr);
        ELSE (* why not? *)
          LookupInThisScope(current^.scope,iPtr^.name,old);
          (* assert: NOT ok ==> old <> NIL *)
          IF (old^.idClass = procHeader) OR
	     (old^.idClass = fwdHeader) THEN (* is elaboration *)
	    (* 11-May-92:
	       Check for second elaboration of an exported procedure.
	       Note that fwdHeaders are changed to procNodes below,
	       but procHeaders must be left for refCount initialisation
	       and C extern declaration *)
	    IF (old^.idClass = procHeader) AND
	       (old^.body # NIL) THEN
	      Error203(old);
	    END;
            CheckParamList(new,old);
(* ! could dispose here *)
            iPtr := old; (* unused IdRec becomes garbage *)
	    IF old^.idClass = fwdHeader THEN old^.idClass := procNode END;
          ELSE
            IF old^.idClass <> unknown THEN Error203(old) END;
            GetParamList(new,iPtr);
            IF old^.idClass = unknown THEN
              (* name on export list, replace by new proc *)
              old^ := iPtr^;
(* ! could dispose here *)
              iPtr := old;
            END;
          END;
        END;
  	iPtr^.frame  := iPtr; (* procedures define their own frame *)
      ELSE 
	ErrSkip(halt,108);
	iPtr := NIL;
      END; (* symbol = ident *)
      IF symbol = semi THEN GetSymbol
      ELSE ErrSkip(halt,105);
      END;
    END ProcHeader;

    PROCEDURE ConstDec(halt : SymbolSet);
      VAR ptr, old : IdDesc;
	  hsh : HashBucketType;
	  ok  : BOOLEAN;
	  exStart, restart, expHalt : SymbolSet;
    BEGIN (* assert: symbol = constSy *)
      GetSymbol;
      restart := halt + SymbolSet{ident,semi};
      expHalt := halt + semiSet;
      exStart := firstExp + expHalt;
      WHILE NOT (symbol IN halt) DO
	IF symbol = ident THEN
	  hsh := lexAtt.hashIx;
	  CreateIdDesc(hsh,ptr,constNode);
	  GetSymbol;
	  IF symbol = equals THEN GetSymbol;
	  ELSE ErrSkip(firstExp,107);
	  END;
	  ConstExpr(expHalt,ptr^.conType,ptr^.conValue);
	  (* 
	     ConstExpr returns the special type marker
	     PointerTo(procTypes) to indicate a procedure
	     constant. In this case, conValue.adrsValue
	     contains the IdDesc of the alias procedure
	  *)
	  IF ptr^.conType = PointerTo(procTypes) THEN (* procedure constant *)
	    ptr^.idClass := conProc;
	    ptr^.procId  := ptr^.conValue.adrsValue;
	  END;
	  (* could test conType <> NIL and tyClass = sets ... *)
	  Commit(); (* make set permanent in string table *)
	  InsertAndCheck(current^,ptr,ok);
	  IF NOT ok THEN
            LookupInThisScope(current^.scope,hsh,old);
            IF old^.idClass = unknown THEN (* overwrite *)
              old^ := ptr^; 
(* ! could dispose here *)
              ptr := old;
            ELSE Error203(old);
            END;
	  END;
	ELSE ErrSkip(restart,108);
	END; (* assert: >= 1 sym consumed OR symbol in restart *)
	IF symbol = semi THEN GetSymbol;
	ELSE ErrSkip(restart,105); (* not sy in restart is ok *)
	END;
      END; (* semi or ident consumed next loop ==> all ok *)
    END ConstDec;

    PROCEDURE VarDec(halt : SymbolSet; storClass : FormalClass);
      VAR idRest, idListRest, seqHalt, tyStart : SymbolSet;
	  hsh   : HashBucketType;
	  ok    : BOOLEAN;
	  idPtr, old : IdDesc;
	  tyPtr : TypeDesc;
	  ids   : Sequence;
	  curs  : ElemPtr;
    BEGIN (* VarDec = varSy { IdentList colon Type semi} *)
      GetSymbol;
      tyStart := halt + firstType;
      idRest := tyStart + 
		   SymbolSet{ident,semi,equals,comma,assignSy,colon};
      idListRest := idRest - SymbolSet{comma,ident}; (* try restart *)
      seqHalt := halt + semiSet;
      InitSequence(ids);
      WHILE NOT (symbol IN halt) DO (* do a declaration sequence *)
	SkipTo(idRest,108);
	LOOP (* do a single ident declaration *)
	  IF symbol = ident THEN
	    hsh := lexAtt.hashIx;
	    CreateIdDesc(hsh,idPtr,varNode);
	(*
	 *  DiagName(hsh);
	 *  StdError.WriteCard(idPtr^.lexLev,0);
	 *  StdError.WriteLn;
	 *)
	    idPtr^.varClass := storClass; (* origMod stays at NIL *)
	    InsertAndCheck(current^,idPtr,ok);
	    IF ok THEN LinkRight(ids,idPtr);
	    ELSE 
	      LookupInThisScope(current^.scope,hsh,old);
              IF old^.idClass = unknown THEN
                old^ := idPtr^;
	(* ! could dispose here *)
                LinkRight(ids,old);
              ELSE Error203(old);
              END;
	    END;
	    GetSymbol;
	  ELSE ErrSkip(idRest,108);
	  END;
         (* ==================================================== *)
         (* ============ new code for alias names ============== *)
         (* ==================================================== *)
         (*         name --> ident[ "[" litstring "]" ].         *)
         (* ==================================================== *)
          IF symbol = lBrac THEN
            IF NOT (ModStateSet{defMod,directMod} <= modState) THEN
              Error(325);
            END;
            GetSymbol;
            IF symbol <> litstring THEN Error(141);
            ELSE
              idPtr^.varOffset := lexAtt.stringIx;
              GetSymbol;
            END;
            SkipTo(idRest + SymbolSet{rBrac},115);
            IF symbol = rBrac THEN GetSymbol END;
          ELSIF ModStateSet{defMod,directMod} <= modState THEN 
            idPtr^.varOffset := 0;
          END;
         (* ==================================================== *)
	  IF symbol = comma THEN GetSymbol;
	  ELSIF symbol IN idListRest THEN EXIT;
	  ELSE ErrSkip(idRest,117);
	  END;
	END; (* single ident declaration *)
	IF symbol = colon THEN GetSymbol;
	ELSE ErrSkip(tyStart,117);
	END;
	Type(seqHalt,tyPtr); (* halt + {semi} *)
        IF (tyPtr <> NIL) AND (tyPtr^.size = 0) THEN 
	  Error(497);	(* no error? *)
	END;
	InitCursor(ids,curs);
	WHILE NOT Ended(curs) DO
	  GetNext(curs,idPtr);
	  idPtr^.varType := tyPtr;
	END;
	DisposeList(ids); (* re-initializes ids *)
	IF symbol = semi THEN GetSymbol ELSE Error(105) END;
      END; (* declaration sequence loop *)
    END VarDec;

    PROCEDURE SearchForEnd(num : CARDINAL);
    BEGIN
      Error(num);
      LOOP
        SkipTo(followDecs,0); (* 0 ==> no errors *)
        IF symbol = endSy THEN
          GetSymbol;
          IF (symbol = ident) AND (lexAtt.hashIx = current^.name) THEN
            Error(139); GetSymbol; RETURN (* resynchronized! *)
          END;
        ELSE RETURN;
        END;
      END;
    END SearchForEnd;

    PROCEDURE MoveParamsToScope(procD : IdDesc);
      VAR index  : CARDINAL;
	  ok     : BOOLEAN;
	  pCrs   : ElemPtr;
	  formal : FormalType;
	  prm    : IdDesc;
	  parent : IdDesc;
	  highId : IdDesc;
	  rootTy : TypeDesc;
	  elemTy : TypeDesc;

    BEGIN
      SuspendList();
      WITH procD^ DO
	InitCursor(procType^.params,pCrs);
	WHILE NOT Ended(pCrs) DO
	  GetNext(pCrs,formal);
	  CreateIdDesc(formal^.fNam,prm,varNode);
	  prm^.varClass := formal^.form;
	  IF formal^.dimN = 0 THEN (* not open array *)
	    prm^.varType := formal^.type;
	  ELSE
	    parent := prm;
	    rootTy := formal^.type;
	    FOR index := 1 TO formal^.dimN DO
	      CreateIdDesc(formal^.fNam,highId,varNode);
	      parent^.nextHigh := highId;	(* forward list *)
	      highId^.hiDepth  := 1;
	      highId^.varClass := openHiForm;
	      highId^.varType  := PointerTo(cards);
	      parent := highId;
	      CreateTypeDesc(thisCompileUnit,elemTy,arrays);
	      elemTy^.elementType := rootTy;	(* backward list *)
	      elemTy^.isDynamic := TRUE;
	      elemTy^.indexType := PointerTo(cards);
	      rootTy := elemTy;
	    END;
	    parent^.nextHigh := NIL;		(* terminate the list *)
	    prm^.varType := rootTy;		(* link to type chain *)
	  END;
	  InsertRef(current^.scope,prm,ok);
	  IF NOT ok THEN ErrIdent(311,prm^.name) END;
	END;
      END; (* with *)
      ResumeList();
    END MoveParamsToScope;

    PROCEDURE ProcDeclaration(halt : SymbolSet;
			  VAR fwPS : Sequence);
      VAR thisId : IdDesc;
	  headNm : CARDINAL;
	  dummy  : TypeDesc;
    BEGIN
      headNm := lastPos.line;
      ProcHeader(halt,thisId);
      (* formal param list is built by ProcHeader *)
      IF thisId = NIL THEN RETURN;
      ELSIF symbol = forwardSy THEN		   (* kjg 11-Aug-89 *)
	thisId^.idClass := fwdHeader; GetSymbol;
	LinkRight(fwPS,thisId);	(* place header on elaboration list *)
      ELSE
	EnterScope(thisId);
	CreateStrucTree(current);
	current^.body^.headerLine := headNm;
	MoveParamsToScope(thisId);
	IF symbol = preconSy THEN
	  IF thisId^.procType^.preCon = NIL THEN
	    PreCondition(thisId^.procType);
	    TraversePrecon(thisId^.procType);
	  ELSE
	    CreateTypeDesc(NIL,dummy,procTypes);
	    dummy^.params := thisId^.procType^.params;
	    PreCondition(dummy);
	    TraversePrecon(dummy);
	    IF NOT EquivPrecons(thisId^.procType^.preCon, dummy^.preCon) THEN 
	      Error(334);
	    END;
	  END;
	END;
	Block(auto);
	(* symbol should be ident here *)
	current^.body^.endIdLine := lastPos.line;
	IF symbol = ident THEN
	  IF lexAtt.hashIx <> thisId^.name THEN Error(200) END;
	  GetSymbol;
	ELSE SearchForEnd(138);
	END;
	ExitScope;
	(*
	 *  must not link if this is only the forward header
	 *  (kjg) 19-Sep-90
	 *)
      END;
      IF symbol = semi THEN GetSymbol ELSE Error(105) END;
    END ProcDeclaration;

    PROCEDURE DoImportList(mod : IdDesc);
      CONST restart = followImport + idSet;
      VAR name : HashBucketType;
	  iPtr : IdDesc;
	  mPtr : IdDesc; (* module name   *)
	  new  : IdDesc; (* temp, for fwdMod overwriting unknown *)
	  cPtr : IdDesc; (* enum con-name *)
	  ok   : BOOLEAN;
	  curs : ElemPtr;
	  exist : IdDesc;
    BEGIN
      LOOP (* import *)
	SkipTo(followImport,109);
	IF symbol = importSy THEN
	  GetSymbol;
          LOOP (* ident list *)
            IF symbol = ident THEN
              name := lexAtt.hashIx;
              Lookup(name,iPtr);
              IF iPtr = NIL THEN
		(* 12-Apr-92: Allow forward import, but check for
		   subsequent elaboration, and don't allow use of a
		   forward type in another declaration *)
		CreateIdDesc(name,iPtr,unknown);
		InsertRef(current^.scope,iPtr,ok);
		LinkRight(current^.fwdImports,iPtr); (* for elab *)
	      END;
	      IF iPtr^.idClass = unknown THEN
		LinkRight(iPtr^.fwdTargets,mod); (* for enums *)
	      END;
              InsertRef(mod^.scope,iPtr,ok);
              IF NOT ok THEN
                LookupInThisScope(mod^.scope,name,cPtr);
                Error203(cPtr);
              ELSIF (iPtr^.idClass = typeNode) AND
                    (iPtr^.typType <> NIL) AND
                    (iPtr^.typType^.tyClass = enums) THEN
                (* insert enumeration constants *)
                InitCursor(iPtr^.typType^.conSeq,curs);
                WHILE NOT Ended(curs) DO
                  GetNext(curs,cPtr);
                  InsertRef(mod^.scope,cPtr,ok);
                  (* Assert(ok) OR errors notified already
                     because names unique in outer scope *)
                END;
              END;
              GetSymbol;
            ELSE Error(108);
            END;
	    IF symbol = comma THEN GetSymbol;
	    ELSIF symbol IN exitSet THEN EXIT;
	    ELSE ErrSkip(restart,110);
	    END;
	  END; (* loop *)
        ELSIF symbol = fromSy THEN (* unqualify imports *)
          GetSymbol;
          IF symbol = ident THEN
            name := lexAtt.hashIx;
            Lookup(name,mPtr);
            IF mPtr = NIL THEN
	      (* 12-Apr-92: As for unqualified imports, allow forward;
		 here we know the id is a module, so also create a forward
		 module node to attach the unknown imported ids *)
	      CreateIdDesc (name, mPtr, fwdMod);
	      InsertRef (current^.scope, mPtr, ok);
	      LinkRight (current^.fwdImports, mPtr);
	    ELSIF mPtr^.idClass = unknown THEN
	      (* convert unknown from previous export to forward module
		 (cf. unknown to module in ModuleDeclaration) *)
	      CreateIdDesc (name, new, fwdMod);
	      mPtr^ := new^;
            ELSIF NOT(mPtr^.idClass IN IdClassSet{exportNode,modNode,fwdMod})
	      THEN
	      ErrSkip(semiSet,280);
            END;
	    IF mPtr^.idClass IN IdClassSet{exportNode,modNode,fwdMod} THEN
              GetSymbol;
              IF symbol = importSy THEN GetSymbol ELSE Error(109) END;
              LOOP (* ident list *)
                IF symbol = ident THEN
                  name := lexAtt.hashIx;
                  LookupInThisScope(mPtr^.scope,name,iPtr);
                  IF iPtr = NIL THEN
		    (* 12-Apr-92: if forward import, add ids to tree of
		       forward module *)
		    IF mPtr^.idClass # fwdMod THEN Error(202);
		    ELSE
		      CreateIdDesc(name,iPtr,unknown);
		      InsertRef(mPtr^.scope,iPtr,ok);
		      (* mPtr will become an exportNode, so elaboration
		       * will be checked by CheckExportsDefined,
		       * but do this anyway for consistent extra
		       * diagnostic?	*)
	              LinkRight(current^.fwdImports,iPtr); (* for elab *)
		      LinkRight(iPtr^.fwdTargets,mod); (* for enums *)
		    END;
		  END;
                  IF iPtr <> NIL THEN
                    InsertRef(mod^.scope,iPtr,ok);
                    IF NOT ok THEN
                      LookupInThisScope(mod^.scope,name,cPtr);
                      Error203(cPtr);
                    ELSIF (iPtr^.idClass = typeNode) AND
                          (iPtr^.typType <> NIL) AND
                          (iPtr^.typType^.tyClass = enums) THEN
                      (* insert enumeration constants *)
                      InitCursor(iPtr^.typType^.conSeq,curs);
                      WHILE NOT Ended(curs) DO
                        GetNext(curs,cPtr);
                        InsertRef(mod^.scope,cPtr,ok);
                        (* but here is different because names were
                           not necessarily visible in outer scope *)
                        IF NOT ok THEN ErrIdent(265,cPtr^.name) END;
                      END;
		    END;
                  END;
                  GetSymbol;
                ELSE Error(108);
                END;
                IF symbol = comma THEN GetSymbol;
                ELSIF symbol IN exitSet THEN EXIT;
                ELSE ErrSkip(restart,110);
                END;
              END;
            END;
          ELSE ErrSkip(semiSet,108);
          END; (* if *)
        ELSE EXIT;
        END;
        IF symbol = semi THEN GetSymbol ELSE Error(105) END;
      END; (* outer loop *)
    END DoImportList;

    PROCEDURE DoExportList(VAR exp : IdDesc); (* export node *)
      CONST exitSet = followDecs + semiSet;
	    restart = exitSet + commaSet + idSet;
      VAR id, old : IdDesc;
	  ok, qual : BOOLEAN;
	  outScope : IdDesc;
	  fwdScope : IdTree;	(* ids in forward unqualifying import *)
    BEGIN
      SkipTo(followDecs + SymbolSet{exportSy},124);
      IF symbol = exportSy THEN
	GetSymbol;
	qual := symbol = qualifiedSy;
	IF qual THEN GetSymbol END;
	outScope := current^.outside;
	LOOP
	  IF symbol = ident THEN
	    CreateIdDesc(lexAtt.hashIx,id,unknown);
	    IF NOT qual THEN (* injection in outside scope *) 
	      InsertAndCheck(outScope^,id,ok);
	      IF NOT ok THEN
	        LookupInThisScope(outScope^.scope,lexAtt.hashIx,old);
	        IF (old^.idClass IN IdClassSet{unknown,procHeader,
					       fwdHeader,fwdMod})   OR
		    IsOwnOpaque(old) THEN
		  id := old;
	        ELSE Error203(old);
	        END;
	      END;
	    END;
           (*
	    *  Insert in export scope first, to see if already there
	    *  from forward import; if so, use that descriptor, but
	    *  carry across the tree of unknown ids (cf ModuleDeclaration);
	    *  also, since the discarded new descriptor may already have
	    *  been an 'old' forward descriptor from the preceding code
	    *  for unqualified export, and so be on the fwdImports list,
	    *  mark it 'resolved' to prevent an elaboration check error.
	    *  There is a danger here: although the scope tree is copied
	    *  to the 'new' descriptor, the old one is still referenced
	    *  by the scope tree of the parent module. Since this only
	    *  occurs when the scope tree was non-empty and so the root
	    *  is fixed, the independent copies of the root pointer
	    *  should remain consistent.
	    *  (see batch program hamburg26.mod for an example) 
            *)
            InsertRef(exp^.scope,id,ok);
	    IF NOT ok THEN
	      LookupInThisScope(exp^.scope,lexAtt.hashIx,old);
	      IF old^.idClass IN IdClassSet{unknown,fwdMod} THEN
		IF id^.idClass = fwdMod THEN
		  Assert(old^.idClass=unknown,"May be existing scope?");
		  old^.idClass := fwdMod;	(* for ModuleDeclaration *)
	          old^.scope := id^.scope;	(* fwdTargets if unknown *)
		END;
		id^.idClass := exportNode;
		id := old;
	      ELSE Error(289);
	      END;
	    END;
	    InsertRef(current^.scope,id,ok); (* decl. in local scope *)
	    (* save scopes for possible elaboration as enumeration type *)
	    IF id^.idClass=unknown THEN
	      LinkRight(id^.fwdTargets,outScope);
	      LinkRight(id^.fwdTargets,current);
	    END;
	    GetSymbol;
	  ELSE ErrSkip(restart,108);
	  END;
	  IF symbol = comma THEN GetSymbol;
	  ELSIF symbol IN exitSet THEN EXIT;
	  ELSE ErrSkip(restart,110);
	  END;
	END;
        IF symbol = semi THEN GetSymbol ELSE Error(105) END;
      END;
    END DoExportList;

    PROCEDURE ModuleDeclaration(halt : SymbolSet;class : FormalClass);
      VAR modDesc, old : IdDesc; stPtr : StatDesc; ok : BOOLEAN;
	  expNode : IdDesc;
	  oldHsh  : HashBucketType;
	  fwdScope : IdTree;	(* ids in forward unqualifying import *)

	PROCEDURE CheckExportsDefined(root : IdTree);
	  VAR save : CARDINAL;
	BEGIN (* pre-order tree-walk *)
	  IF root = NIL THEN RETURN;
	  ELSE
	    IF root^.ident^.idClass = unknown THEN
	      save := lastPos.line;
	      lastPos.line := current^.body^.headerLine;
	      ErrIdent(230,root^.name);
	      lastPos.line := save;
	    END;
	    CheckExportsDefined(root^.left);
	    CheckExportsDefined(root^.right);
	  END;
	END CheckExportsDefined;

    BEGIN
      GetSymbol; (* moduleSy *)
      SkipTo(idSet,108);
      IF symbol = eofSy THEN RETURN END;
      (* now generate inline call to module body *)
      CreateIdDesc(lexAtt.hashIx,modDesc,modNode);
      CreateIdDesc(lexAtt.hashIx,expNode,exportNode);
		(* ?should the exportNode have a ref to the modNode? *)
      InsertAndCheck(current^,expNode,ok);
      IF NOT ok THEN
	LookupInThisScope(current^.scope,lexAtt.hashIx,old);
	(* 12-Apr-92: forward module will have a tree of unknown ids *)
	IF old^.idClass IN IdClassSet{unknown,fwdMod} THEN
	  IF old^.idClass = fwdMod THEN
	    fwdScope := old^.scope;
	  ELSE
	    fwdScope := NIL;	(* scope is part of fwdTargets if unknown *)
	  END;
	  old^ := expNode^; expNode := old;
	  expNode^.scope := fwdScope;
	ELSE ErrIdent(264,lexAtt.hashIx);
	END;
      END;
      WITH modDesc^ DO
	uphill  := pervasiveUnit;
(*
 *  redundant, done by EnterScope anyhow
 *      outside := current;
 *)
	frame   := current^.frame;
      END;
      CreateStrucTree(modDesc);		(* attach body to modDesc *)
      oldHsh := unitName;
      unitName := lexAtt.hashIx;
      GetSymbol; (* ident *)
      IF symbol = lBrac THEN (* priority *)
        ErrSkip(semiSet,509);
      ELSE SkipTo(semiSet,105);
      END;
      IF symbol = eofSy THEN RETURN END;
      GetSymbol; (* semi *)
      DoImportList(modDesc);
      EnterScope(modDesc);	(* modDesc becomes current *)

      DoExportList(expNode);

      InitSequence(current^.fwdImports); (* 12-Apr-92 *)
      Block(class); (* inherited attribute *)
      (* symbol should be ident here *)
      IF symbol = ident THEN
	current^.body^.endIdLine := lastPos.line;
	IF lexAtt.hashIx <> modDesc^.name THEN Error(200) END;
	GetSymbol;
      ELSE SearchForEnd(138);
      END;
      CheckElaboration(current^.fwdImports);
      ExitScope;		(* outside becomes current again *)
      CheckExportsDefined(expNode^.scope);
      IF symbol = semi THEN GetSymbol ELSE Error(105) END;
      unitName := oldHsh;
    END ModuleDeclaration;

    PROCEDURE Declarations(varClass : FormalClass);
    (* Declaration = constSy {ident equals ConstExpr semi}
		  | typeSy { ident equals Type semi}
		  | varSy { IdentList colon Type semi}
		  | ProcDec semi | ModDec semi .		 *)
      VAR bpList : Sequence; (* of pointer TypeDesc to backpatch *)
	  fwList : Sequence; (* of forward headers to check for  *)
	  varCls : FormalClass;
    BEGIN
      InitSequence(bpList); InitSequence(fwList);
      LOOP
	CASE symbol OF
	| constSy : ConstDec(followDecs);
	| typeSy  : TypeDec(followDecs, bpList);
	| varSy   : VarDec(followDecs, varClass);
	| moduleSy :
	    ModuleDeclaration(followDecs,varClass);
	| procedureSy :
	    ProcDeclaration(followDecs, fwList); (* always "auto" *)
	| eofSy, beginSy, endSy : EXIT;
	ELSE ErrSkip(followDecs,106);
	END;
      END; (* loop *)
      CheckElaboration(fwList); BackPatch(bpList);
      DisposeList(bpList); DisposeList(fwList);
    END Declarations;

    PROCEDURE Definitions;
      VAR bpList : Sequence; (* of pointer TypeDesc to backpatch *)
	  header : IdDesc;   (* scratch variable: add to current *)
    BEGIN
      InitSequence(bpList);
      LOOP
	CASE symbol OF
	| constSy : ConstDec(followDefs);
	| typeSy  : TypeDec(followDefs, bpList);
	| varSy   : VarDec(followDefs,static(*any*));
	| procedureSy :
	    ProcHeader(followDefs,header);
	    IF symbol = preconSy THEN
	      IF header <> NIL THEN
		EnterScope(header);
		MoveParamsToScope(header);
		PreCondition(header^.procType);
		TraversePrecon(header^.procType);
		ExitScope;
	      END;
	    END;
	| eofSy, endSy : EXIT;
	ELSE ErrSkip(followDefs,106);
	END;
      END; (* loop *)
      BackPatch(bpList);
      DisposeList(bpList);
    END Definitions;

    PROCEDURE IfStatement(halt : SymbolSet;
                          desc : StatDesc);  (* already linked *)
      VAR new : SymbolSet;
          branch : IfDesc;
    BEGIN
      new := halt + SymbolSet{thenSy,elseSy,elsifSy};
      REPEAT (* assert: symbol is in {ifSy,elsifSy} *)
        GetSymbol; 
        CreateConditional(branch);
        LinkRight(desc^.branches,branch);
        WITH branch^ DO
          Expression(new,condition);
	  IF symbol <> thenSy THEN ErrSkip(new,133) END;
          IF symbol = thenSy THEN GetSymbol END;
          StatementSequence(new,statSeq);
        END; (* with *)
        SkipTo(new,103);
      UNTIL symbol <> elsifSy;
      IF symbol = elseSy THEN
        GetSymbol;
        CreateConditional(branch);
        LinkRight(desc^.branches,branch);
        StatementSequence(halt,branch^.statSeq);
        SkipTo(halt,103);
      END;
      IF symbol = endSy THEN GetSymbol;
      ELSE Error(103);
      END;
    END IfStatement;

    PROCEDURE OneCase(halt : SymbolSet; desc : StatDesc);
      VAR new, restart : SymbolSet;
          case : CaseDesc;
    BEGIN
      IF symbol IN firstExp THEN
        WITH desc^ DO
          CreateCaseDesc(case);
          LinkRight(desc^.cases,case);
          new := halt + SymbolSet{colon,comma};
          restart := halt + firstExp;
          (* now get ranges *)
          LOOP
            GetCaseRange(new,case^.selRnges);
            IF symbol = comma THEN GetSymbol;
            ELSIF symbol IN new THEN EXIT; (* commas already gone *)
            ELSE ErrSkip(restart,110);
            END;
          END;
          IF symbol = colon THEN
            GetSymbol;
            StatementSequence(halt,case^.statSeq);
          ELSE ErrSkip(halt,117);
          END;
        END; (* with *)
      END; (* if *)
    END OneCase;

    PROCEDURE CaseStatement(halt : SymbolSet;
                            desc : StatDesc);
      VAR new, restart : SymbolSet;
    BEGIN
      new := halt + SymbolSet{ofSy,bar,elseSy};
      restart := new + firstExp;
      GetSymbol;
      Expression(new,desc^.caseInfo^.switch);
      IF symbol = ofSy THEN
        GetSymbol; EXCL(new,ofSy);
      ELSE ErrSkip(restart,116);
      END;
      LOOP
        OneCase(new,desc);
        IF symbol = bar THEN GetSymbol;
        ELSIF symbol IN new THEN EXIT;
        ELSE ErrSkip(restart,123);
        END;
      END;
      IF symbol = elseSy THEN
        GetSymbol;
        StatementSequence(halt,desc^.default);
      ELSE InitSequence(desc^.default);
      END;
      IF symbol = endSy THEN GetSymbol;
      ELSE ErrSkip(halt,103);
      END;
    END CaseStatement;

    PROCEDURE ForStatement(halt : SymbolSet;
                           desc : StatDesc);
      VAR new : SymbolSet;
          stepType  : TypeDesc;
          stepValue : LexAttType;
    BEGIN
      GetSymbol;
      new := halt + SymbolSet{toSy,bySy,doSy};
      WITH desc^ DO
        IF symbol <> ident THEN ErrSkip(new + idSet,108) END;
        IF symbol = ident THEN
          LookupInThisScope(current^.scope,
                            lexAtt.hashIx,controlVariable);
          IF controlVariable = NIL THEN
            (* 02Apr97: Not found in the local scope, but is it global? *)
            Lookup(lexAtt.hashIx,controlVariable);
            IF controlVariable = NIL THEN Error(204);   (* 'not known' *)
            ELSE
              Error(239);                               (* 'must be local' *)
              controlVariable := NIL;   (* treat as if not known *)
            END;
          ELSE
            WITH controlVariable^ DO
              IF idClass <> varNode THEN Error(235);
              ELSIF NOT IsOrdinalType(varType) THEN Error(206);
              ELSIF varClass > static THEN
                IF varClass >= valForm THEN
                  Error(240); (* must not be formal param *)
                ELSE Error(241); (* must not be imported or exported *)
                END;
              END;
            END; (* with *)
          END;
          GetSymbol;
          IF symbol <> assignSy THEN Error(131);
          ELSE GetSymbol; Expression(new,initial);
          END;
        END; (* of if ident *)
        IF symbol <> toSy THEN ErrSkip(new,132) END;
        EXCL(new,toSy);
        IF symbol = toSy THEN
          GetSymbol;
          Expression(new,final);
        END;
        SkipTo(new,120); EXCL(new,bySy); 
        IF symbol = bySy THEN
          GetSymbol;
          ConstExpr(new,stepType,stepValue);
          (* check: is it compatible with integer? *)
          IF (Compatible(stepType,PointerTo(ints))) AND
		     (stepValue.intValue <> 0) THEN		(* Oct 92 *)
            stepSize := stepValue.intValue;
          ELSE Error(238);
          END;
          SkipTo(new,129);
        END;
        IF symbol = doSy THEN GetSymbol;
        ELSE ErrSkip(halt,129);
        END;
        StatementSequence(halt,forBody);
      END; (* with *)
      IF symbol = endSy THEN GetSymbol
      ELSE ErrSkip(halt,103);
      END;
    END ForStatement;

    PROCEDURE StatementSequence(halt : SymbolSet;
                            VAR sequ : Sequence);
      VAR restart, default, desEnd, new : SymbolSet;
          ptr : StatDesc;
    BEGIN
      restart := halt + firstStat;  (* starters of NON-EMPTY stats *)
      default := restart + semiSet; (* assert: endSy is in halt    *)
      desEnd  := default + SymbolSet{assignSy,lPar};
      LOOP
        new := default;
        CASE symbol OF
        | ident    :
            CreateStatDesc(ptr,assignNode);
            LinkRight(sequ,ptr);
            ParseDesignator(desEnd,ptr^.designator);
	    SkipTo(desEnd,131);
            IF symbol = assignSy THEN
              GetSymbol;
              Expression(default,ptr^.expression);
            ELSIF symbol = lPar THEN
              INCL(new,rPar);
              ptr^.statClass := procCallNode;
              GetSymbol;
              IF symbol = rPar THEN GetSymbol;
              ELSE
                ActualParams(new,ptr^.actualParams);
                IF symbol = rPar THEN GetSymbol;
                ELSE Error(111);
                END;
              END;
            ELSIF symbol IN default THEN
              ptr^.statClass := procCallNode;
            ELSE Error(128);
            END;
        | whileSy  :
            CreateStatDesc(ptr,whileNode);
            LinkRight(sequ,ptr);
            GetSymbol; INCL(new,doSy);
            Expression(new,ptr^.condition);
            IF symbol = doSy THEN GetSymbol
            ELSE ErrSkip(restart,129);
            END;
            StatementSequence(halt,ptr^.wrBody); (* endSy already IN *)
            IF symbol = endSy THEN GetSymbol
            ELSE ErrSkip(restart,103);
            END;
        | loopSy   :
            CreateStatDesc(ptr,loopNode);
            LinkRight(sequ,ptr); GetSymbol;
            StatementSequence(halt,ptr^.loopBody); (* endSy already IN *)
            IF symbol = endSy THEN GetSymbol
            ELSE ErrSkip(restart,103);
            END;
        | repeatSy :
            CreateStatDesc(ptr,repeatNode);
            LinkRight(sequ,ptr);
            GetSymbol; INCL(new,untilSy);
            StatementSequence(new,ptr^.wrBody); (* endSy already IN *)
	    IF symbol <> untilSy THEN ErrSkip(new,130) END;
            IF symbol = untilSy THEN
              GetSymbol;
              Expression(default,ptr^.condition);
            ELSE ErrSkip(halt,130);
            END;
        | withSy   :
            GetSymbol; INCL(new,doSy);
            CreateStatDesc(ptr,withNode); (* srcPos = desig pos *)
            LinkRight(sequ,ptr);
            ParseDesignator(new,ptr^.withInfo^.desig);
            IF symbol = doSy THEN GetSymbol
            ELSE ErrSkip(restart,129);
            END;
            StatementSequence(halt,ptr^.withBody); (* endSy already IN *)
            IF symbol = endSy THEN GetSymbol
            ELSE ErrSkip(restart,103);
            END;
        | caseSy   :
            CreateStatDesc(ptr,caseNode);
            LinkRight(sequ,ptr);
            CaseStatement(default,ptr);
        | forSy    : 
            CreateStatDesc(ptr,forNode);
            LinkRight(sequ,ptr);
            ForStatement(default,ptr);
        | ifSy :
            CreateStatDesc(ptr,ifNode);
            LinkRight(sequ,ptr);
            IfStatement(default,ptr);
        | exitSy   :
            CreateStatDesc(ptr,exitNode);
            LinkRight(sequ,ptr); GetSymbol;
        | returnSy :
            CreateStatDesc(ptr,returnNode);
            LinkRight(sequ,ptr); GetSymbol;
            IF symbol IN firstExp THEN
              Expression(default,ptr^.returnResult);
            END;
        | retrySy :
            CreateStatDesc(ptr,retryNode);
            LinkRight(sequ,ptr); GetSymbol;
        ELSE (* empty statement ==> nothing *)
        END;
        IF symbol = semi THEN GetSymbol;
        ELSIF (symbol = ident) AND
              (lexAtt.hashIx = current^.name) THEN
          Error(137); EXIT;
        ELSIF symbol IN firstStat THEN Error(105); (* missing ";" *)
        ELSIF symbol IN halt THEN EXIT; (* normal exit *)
        ELSE ErrSkip(restart,105); (* insertion error *)
        END;
      END;
    END StatementSequence;

    PROCEDURE Block(varCls : FormalClass);
      VAR exceptStuff : SymbolSet;
    BEGIN (* scope is known through state variable "current" *)
      IF varCls = auto THEN
	exceptStuff := SymbolSet{exceptSy};
      ELSE
	exceptStuff := SymbolSet{exceptSy,finallySy};
      END;
      Declarations(varCls);
      IF symbol = beginSy THEN
        GetSymbol;
        StatementSequence(followDecs + exceptStuff, current^.body^.statements);
       (* get the except sequence if present*)
        IF symbol = exceptSy THEN
	  IF NOT exceptOK THEN Error(298) END;
          GetSymbol;
          StatementSequence(followDecs + exceptStuff - SymbolSet{exceptSy},
 				current^.body^.exceptSeq);
        END;
       (* get the finalisation sequences if present*)
        IF symbol = finallySy THEN
          GetSymbol;
          StatementSequence(followDecs + SymbolSet{exceptSy},
				current^.body^.finalSeq);
          IF symbol = exceptSy THEN
	    IF NOT exceptOK THEN Error(298) END;
            GetSymbol;
            StatementSequence(followDecs, current^.body^.finalExSeq);
          END;
	END;
      ELSIF symbol <> endSy THEN Error(136);
      END;
      IF symbol = endSy THEN GetSymbol;
      ELSIF (symbol <> ident) OR
            (lexAtt.hashIx <> current^.name) THEN Error(103);
      (* else error 137 already notified *)
      END;
    END Block;

    PROCEDURE CompModHeader();
    (* compilation unit header *)
    BEGIN (* CompModHeader = moduleSy ident semi *)
      IF symbol <> moduleSy THEN
        ErrSkip(SymbolSet{moduleSy,ident,semi,eofSy},100);
      END;
      IF symbol = moduleSy THEN GetSymbol END;
      SkipTo(idSet,108);
      IF symbol = ident THEN
	unitName := lexAtt.hashIx;
	CreateIdDesc(unitName,thisCompileUnit,modNode);
	thisCompileUnit^.uphill  := pervasiveUnit;
	thisCompileUnit^.frame   := thisCompileUnit; (* the global frame *)
	GetSymbol;
	EnterScope(thisCompileUnit);
        CreateStrucTree(current);
      END;
      IF symbol = lBrac THEN (* priority *)
        ErrSkip(semiSet,509);
      ELSIF symbol <> semi THEN
	SkipTo(semiSet,105);
      END;
      IF symbol = semi THEN GetSymbol END;
    END CompModHeader;

    VAR firstSym : TerminalSymbols; (* local static variable *)

    PROCEDURE ParseFileHeader;
    (* precondition  : an input file is attached and options set *)
    (* postcondition : the file header and imports are parsed    *)

      (* The following depends on a perverse side-effect of  *)
      (* !pragma! recognition: the bkt num is left in lexAtt *)
       PROCEDURE SetStatePragmaFlags();
       BEGIN
         IF lexAtt.hashIx = sysBkt THEN
           INCL(modState,sysMod); INCL(modState,nonRec);
         ELSIF (lexAtt.hashIx = directBkt) THEN
	   RelaxLexicalRules();
	   INCL(modState,macroMod);
	   INCL(modState,directMod);
         ELSIF (lexAtt.hashIx = foreignBkt) THEN
	   INCL(modState,macroMod);
         ELSIF (lexAtt.hashIx = nonRecBkt) OR
               (lexAtt.hashIx = libBkt) THEN
	   INCL(modState,nonRec);
         END;
       END SetStatePragmaFlags;
      (* the next symbol-read attribute erases the value.    *)

      VAR   localState : ModStateSet;

    BEGIN  (* CompUnit = ProgModule | DefModule | ImplModule. *)
      localState := ModStateSet{};
      OpenInput; 
      IF NOT (extensions IN modState) THEN ExcludeExt; ExclStrExt END;
      InitScanner;
      WHILE symbol = ident DO
	IF    lexAtt.hashIx = retCutBkt  THEN 
	  INCL(localState,retCutAll);
	ELSIF lexAtt.hashIx = foreignBkt THEN 
	  INCL(localState,macroMod);
	ELSIF lexAtt.hashIx = directBkt  THEN 
	  INCL(localState,directMod);
	  INCL(localState,macroMod);
	ELSE  Error(100);
	END;
	GetSymbol;
      END;
      firstSym := symbol;
      CASE symbol OF
     (* --------------------------------------------- *)
      |  implementationSy :
	   IF localState <> ModStateSet{} THEN Error(100) END;
           INCL(modState,impMod); GetSymbol;
           CompModHeader();
           ImportOwnSyms;
           CompImports;
     (* --------------------------------------------- *)
      | definitionSy :
           SetStatePragmaFlags();
           INCL(modState,defMod); GetSymbol;
	   modState := modState + localState;
           CompModHeader();
           StartImportList();
	   CompImports;
     (* --------------------------------------------- *)
      | moduleSy :
	   IF localState <> ModStateSet{} THEN Error(100) END;
           INCL(modState,progMod);
           CompModHeader();
           CompImports;
     (* --------------------------------------------- *)
      ELSE SetFlagOn(filErrors);
      END;
     (* --------------------------------------------- *)
    END ParseFileHeader;

    PROCEDURE ParseInputFile;
    (* precondition  : file header parsed by ParseFileHeader  *)
    (* postcondition : a valid tree is constructed. If errors not
                       in M2Scanner.CurrentFlags() then file was a
                       syntactically correct Modula program.  *)
    BEGIN  (* CompUnit = ProgModule | DefModule | ImplModule. *)
      IF filErrors IN CurrentFlags() THEN RETURN END;
      IF firstSym = definitionSy THEN
        IF symbol = exportSy THEN ErrSkip(followDecs,502) END;
        StartExportList();
        Definitions;
        IF symbol <> endSy THEN
          ErrSkip(SymbolSet{endSy,ident,dot,semi},104);
        END;
        IF symbol = endSy THEN GetSymbol END;
      ELSE
	InitSequence(opaqFrms); 
	InitSequence(fwdGlobs);
        InitSequence(current^.fwdImports); (* 12-Apr-92 *)
        Block(static);
(*
 *  code now uses body^.headerLine ...
 *      current^.body^.visitDepth := lastPos.line;
 *)
        (* 12-Apr-92: check for elaboration of forward imports *)
        CheckElaboration(current^.fwdImports);
        IF firstSym = implementationSy THEN 
	  CheckElaboration(fwdGlobs); 
	  CheckElaboration(unitImports); 
	  ResolveFormals;
	END;
      END;
      IF symbol = ident THEN (* check for match *)
	current^.body^.endIdLine := lastPos.line;
        IF thisCompileUnit^.name <> lexAtt.hashIx THEN
          Error(200);
        END;
        GetSymbol;
      ELSE SearchForEnd(101);
      END;
      SkipTo(SymbolSet{dot},102);
      IF symbol = dot THEN GetSymbol END;
      SkipTo(SymbolSet{eofSy},500);
      (*
       *  the traversal phase places many new strings in
       *  the string table ... therefore must make the 
       *  current highTide mark safe from overwriting
       *)
       Commit;
    END ParseInputFile;

(***************************************************************)

END M2Parser.
