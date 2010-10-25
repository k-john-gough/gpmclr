(****************************************************************)
(*                                                              *)
(*              Modula-2 Compiler Source Module                 *)
(*                                                              *)
(*  Code generator state for the currently compiling procedure  *)
(*                                                              *)
(*     (c) copyright 1990 Faculty of Information Technology     *)
(*                                                              *)
(*      original module : kjg February 1990                     *)
(*      modifications   : dwc Apr  params 2 byte aligned        *)
(*                      : kjg func returning REAL     20-Jun-91 *)
(*			: kjg callee copy val recs    17-Oct-92 *)
(*								*)
(*   =============== merged mips and i386 source ============	*)
(*			   kjg 22 Mar 93			*)
(*                                                              *)
(****************************************************************
$Log: m2procst.mod,v $
Revision 1.13  1997/01/16 04:48:14  gough
        LookupInThisScope, now uses linkName field.

Revision 1.12  1996/11/27 02:36:37  lederman
use codeBlkList instead of unitExports

Revision 1.11  1996/05/10 06:53:05  lederman
make parSiz param. of GetActuals an INTEGER

Revision 1.10  1995/10/10 23:32:47  lederman
DCode V3 stuff

# Revision 1.9  1995/03/24  08:26:38  gough
# FormalSize must take into account multiple highs from multidim open arrays
#
# Revision 1.8  1995/03/23  23:03:22  gough
# allocate offsets for _multiple_ high parameter values
#
# Revision 1.7  1995/03/14  01:45:31  gough
# IsCopyParam is changed, and auto class variables in the initialisation
# part are still given offsets by procedure DoBaseOffsets
#
# Revision 1.6  1994/10/12  06:00:42  lederman
# change GetActuals to handle retCut and parsFixed returning -ve parSize
#
# Revision 1.5  1994/10/11  07:17:24  gough
# separate concepts of IsRefParam and IsCopyParam
#
# Revision 1.4  1994/09/19  04:22:38  lederman
# if expandTests evaluate all parameters before emitting mkPar's (GetActuals)
#
# Revision 1.3  1994/07/15  03:17:05  lederman
# align all LOCALs to at least quad-alignment
#
# Revision 1.2  1994/07/01  05:22:01  lederman
# change all literal 4's to bytesInWord etc.
#
*****************************************************************
Revision 1.5  93/11/16  08:59:44  gough
send back parBytes = 0 in case of retCut procedures

Revision 1.4  93/11/11  09:24:55  gough
remove assignment of unused attribute

Revision 1.3  93/05/31  13:38:44  goughh
big-endian offset fix for param sizes less than 4.
*****************************************************************)

IMPLEMENTATION MODULE M2ProcState;

IMPORT StdError, Types, M2NodeDefs;
FROM M2NameHandler IMPORT GetSourceRep;
FROM M2InOut IMPORT DiagName;

  FROM SYSTEM IMPORT CAST, ADR;
  FROM Storage IMPORT ALLOCATE;
  FROM ProgArgs IMPORT Assert;
  FROM M2Alphabets IMPORT ModStateFlags;
  FROM M2NodeDefs IMPORT 
	modState,
	IdDesc, IdRec, IdTree, TypeDesc, TypeRec,
	FormalClass, FormalType, FormalRec,
	IdNodeClass, TyNodeClass,
	StrucTree, StrucRec,
	infinity, Attribute, AttributeSet,
	codeBlkList, thisCompileUnit;
  FROM GenSequenceSupport IMPORT
	Sequence, ElemPtr, LengthOf,
	InitSequence, LinkLeft, LinkRight,
	InitCursor, GetNext, Ended;
  FROM M2SSUtilities IMPORT procCost, HasCalls, LookupInThisScope;
  FROM M2TabInitialize IMPORT PointerTo;
  FROM M2Designators IMPORT 
	ActualParMode, ExprDesc, ExprNodeClass;

  FROM M2MachineConstants IMPORT 
	alignMap, paramMap, stackMarkSize, displayElSize, expandTests,
	stackInverted, adrSize, bytesInWord, crossEndian, bigEndian,
	refRecords, sunStructs, extRecRetPtr, extArrRetPtr, parsFixed;

(*
 *  definitions from the def file
 *
 *  VAR isMain : BOOLEAN; (* read only ! *)
 *
 *  The following state variable is used to keep track
 *  of the current procedure environment of the code
 *
 *   VAR tmpOffset  : INTEGER;
 *   VAR copyOffset : INTEGER;
 *   VAR current    : IdDesc;
 *)

(*
 *  The offset calculations are done as follows:
 *  * local (auto) variables and val params are allocated
 *    space and have the varOffset field set in the IdRec
 *  * space is allocated to (fixed size) value array copies
 *    with the offset being modified *after* the copy
 *    code is emitted
 *  * all params have the varOffset field set in the IdRec
 *)
    VAR   cOffset : INTEGER;
	  predArgSiz : INTEGER; (* presumed arg size *)
	  dummy   : IdRec;

(*==============================================================*)

    PROCEDURE Align(VAR offset : INTEGER;
			align  : CHAR);
      VAR mask : INTEGER;
    BEGIN
      mask    := ORD(align);
      offset  := CAST(CARDINAL,
		     CAST(BITSET,(offset + mask)) - CAST(BITSET,mask));
    END Align;

    PROCEDURE NeedsDestPtr(ty : TypeDesc) : BOOLEAN;
    BEGIN
      WITH ty^ DO
        RETURN (result <> NIL) AND 
	((* either *) 
		NOT extRecRetPtr AND (result^.tyClass = records)
          OR
		NOT extArrRetPtr AND 
		((result^.tyClass = arrays)  OR
		 (result^.tyClass = sets) AND (result^.size > bytesInWord)
		)
	);
      END;
    END NeedsDestPtr;

    PROCEDURE IsCopyParam(ty : TypeDesc) : BOOLEAN;
    (* now (17 Oct 92) records are copied by the *)
    (* callee if the flag refRecords is true     *)
    (* ==> there is a local copy of a ref param  *)
    BEGIN
      RETURN ((ty^.tyClass = arrays) AND NOT ty^.isDynamic) OR
	     ((ty^.tyClass = sets) AND (ty^.size > bytesInWord)) OR
	     ((ty^.tyClass = records) AND (refRecords AND NOT sunStructs));
    END IsCopyParam;

    PROCEDURE IsRefParam(ty : TypeDesc) : BOOLEAN;
    (* now (17 Oct 92) records are copied by the *)
    (* callee if the flag refRecords is true     *)
    (* ==> the actual param is referenced by ptr *)
    BEGIN
      RETURN (ty^.tyClass = arrays) OR
	     ((ty^.tyClass = records) AND refRecords) OR
	     ((ty^.tyClass = sets) AND (ty^.size > bytesInWord));
    END IsRefParam;

(*==============================================================*)

  MODULE ActualParams;

    IMPORT modState, ModStateFlags, Types, expandTests,
	TypeDesc, IdDesc, TypeRec, IdRec, thisCompileUnit,
	TyNodeClass, IdNodeClass, ExprDesc, ExprNodeClass,
	InitSequence, LinkLeft, LinkRight, Sequence, 
	ElemPtr, GetNext, Ended, InitCursor, LengthOf,
	FormalClass, FormalType, FormalRec, 
	ActualParMode, DiagName,
        parsFixed, procCost, bigEndian, crossEndian,
	HasCalls, IsCopyParam, IsRefParam, NeedsDestPtr, Align, 
	PointerTo, stackInverted, alignMap, paramMap,
	adrSize, bytesInWord, ParInfo, StdError, Assert, ALLOCATE;

    EXPORT GetActuals, FormalSize, LexLevel;

    PROCEDURE LexLevel(id : IdDesc) : Types.Card8;
      VAR count : Types.Card8;
    BEGIN
      count := 0;
      LOOP
        CASE id^.idClass OF
        | procHeader, procNode :
	    INC(count);
	    id := id^.uphill;
	| exportNode :
	    id := id^.outside; (* no inc *)
	| modNode :
	    RETURN count;
        END;
      END;
    END LexLevel;

    PROCEDURE FormalSize(frmTy : TypeDesc) : CARDINAL;
      VAR fCurs  : ElemPtr;
	  formal : FormalType;
	  total  : INTEGER;
	  isInt, isExt  : BOOLEAN;
      (* this code is stack-direction independent *)
    BEGIN
      total := 0;
      isExt := (frmTy^.parentMod^.idClass = exportNode) AND
                      frmTy^.parentMod^.macro;
      isInt := (frmTy^.parentMod^.idClass = exportNode) AND
                      frmTy^.parentMod^.direct;
      IF NeedsDestPtr(frmTy) THEN INC(total,adrSize) END;
      InitCursor(frmTy^.params,fCurs);
      WHILE NOT Ended(fCurs) DO
	GetNext(fCurs,formal);
	IF (formal^.form <> valForm) OR
	    IsRefParam(formal^.type) THEN 
	  Align(total,alignMap[adrSize]);
	  INC(total,adrSize);	(* Oct 92 *)
	ELSE 
	  Align(total,paramMap[formal^.type^.alignMask]);
	  INC(total,formal^.type^.size);
        END;
	IF (formal^.form >= openValForm) AND
	    NOT isInt THEN (* do extra param(s) for high(s) *)
	  INC(total,bytesInWord * formal^.dimN);
	END;
      END;
      Align(total,paramMap[0C]);
      RETURN total;
    END FormalSize;

    PROCEDURE GetActuals(inSeq : Sequence;
			 frmTy : TypeDesc;
		     VAR parSiz : INTEGER;
		     VAR outSq1 : Sequence;
		     VAR outSq2 : Sequence);

      VAR eCurs  : ElemPtr;
	  actual : ExprDesc;
	  fCurs  : ElemPtr;
	  formal : FormalType;
	  param  : ParInfo;
	  outSq  : Sequence;
	  isExt  : BOOLEAN;
	  isInt  : BOOLEAN;
	  noCut  : BOOLEAN;

	  total  : INTEGER;
	  pSize  : INTEGER;
	  targetBig : BOOLEAN;
	  highCount : CARDINAL;

    BEGIN
      total := 0;
      targetBig := bigEndian <> crossEndian;
      isExt := (frmTy^.parentMod^.idClass = exportNode) AND
                      frmTy^.parentMod^.macro;
      isInt := (frmTy^.parentMod^.idClass = exportNode) AND
                      frmTy^.parentMod^.direct;
      noCut :=  (frmTy^.parentMod = thisCompileUnit) AND
				(retCutAll IN modState)	OR
		(frmTy^.parentMod^.idClass = exportNode) AND 
				frmTy^.parentMod^.retCut;
      IF NeedsDestPtr(frmTy) THEN INC(total,adrSize) END;
      InitSequence(outSq);
      InitSequence(outSq1);
      InitSequence(outSq2);
      InitCursor(inSeq,eCurs);
      InitCursor(frmTy^.params,fCurs);
      IF stackInverted THEN
        WHILE NOT Ended(eCurs) DO
	  GetNext(eCurs,actual);
	  GetNext(fCurs,formal);
	  NEW(param);
	  WITH param^ DO
	    expr := actual;
	    dTyp := formal^.type;
	  END;
	  IF (formal^.form <> valForm) OR
	      IsRefParam(formal^.type) THEN 
	    Align(total,alignMap[adrSize]);
	    param^.ofst := total;
	    INC(total,adrSize);	(* Oct 92 *)
	  ELSE 
	    Align(total,paramMap[formal^.type^.alignMask]);
	    pSize := formal^.type^.size;
	   (*
	    *  adjust for bytes and halfwords being at
	    *  at the "wrong" end of the param word.
	    *)
	    IF (pSize < INT(bytesInWord)) AND targetBig THEN 
	      param^.ofst := total + INT(bytesInWord) - pSize;
	    ELSE
	      param^.ofst := total;
	    END;
	    INC(total,pSize);
          END;
	  LinkLeft(outSq,param);
(*
 *  IF (formal^.form = openValForm) THEN
 *    IF actual^.exprClass = desigNode THEN
 *      IF actual^.name.variable^.varType^.isDynamic THEN
 *        StdError.WriteString("Passing open <");
 *      ELSE
 *        StdError.WriteString("Passing fixed <");
 *      END;
 *      DiagName(actual^.name.variable^.name);
 *    ELSIF actual^.exprClass = literalNode THEN
 *      StdError.WriteString("Passing literal <");
 *    END;
 *    StdError.WriteString("> to value open" + 12C);
 *  END;
 *)
	  IF (formal^.form >= openValForm) AND
	      NOT isInt THEN (* do extra param for high *)
	    FOR highCount := 1 TO formal^.dimN DO
	      GetNext(eCurs,actual);
	      NEW(param);
	      WITH param^ DO
	        expr := actual;
	        dTyp := PointerTo(cards);
	        ofst := total; 
	      END;
	      INC(total,bytesInWord);
	      LinkLeft(outSq,param);
	    END;
	  END;
	  Align(total,paramMap[0C]);
        END; (* end while *)
      ELSE	(* stack upright *)
        WHILE NOT Ended(eCurs) DO
	  GetNext(eCurs,actual);
	  GetNext(fCurs,formal);
	  IF (formal^.form <> valForm) OR
	      IsRefParam(formal^.type) THEN INC(total,bytesInWord); (* Oct 92 *)
	  ELSE INC(total,formal^.type^.size);
          END;
	  Align(total,paramMap[formal^.type^.alignMask]);
	  NEW(param);
	  WITH param^ DO
	    expr := actual;
	    dTyp := formal^.type;
	    ofst := -total;
	  END;
	  LinkLeft(outSq,param);
	  IF (formal^.form >= openValForm) AND
	      NOT isInt THEN (* do extra param for high *)
	    FOR highCount := 1 TO formal^.dimN DO
	      GetNext(eCurs,actual);
	      NEW(param);
	      INC(total,bytesInWord);
	      WITH param^ DO
	        expr := actual;
	        dTyp := PointerTo(cards);
	        ofst := -total; 
	      END;
	      LinkLeft(outSq,param);
	    END;
	  END;
	  Align(total,paramMap[0C]);
        END; (* end while *)
      END;  (* if stack inverted *)
      IF NOT parsFixed THEN
	outSq2 := outSq;
      ELSE
	InitCursor(outSq,eCurs);
	WHILE NOT Ended(eCurs) DO
	  GetNext(eCurs,param);
	 (*
	  * Colouring allocators don't generate correct allocations
	  * in the presence of inline tests during parameter assembly.
	  * ExprCost() could check for these tests (?) but this is
	  * simpler and generates perfectly good code. ( jl Sep 94 )
	  *)
	  IF expandTests OR HasCalls(param^.expr) THEN
	    LinkRight(outSq1,param);
	  ELSE LinkRight(outSq2,param);
	  END;
	END;
      END;
      IF noCut <> parsFixed THEN
	parSiz := 0
      ELSIF parsFixed THEN	(* jl Oct 94 *)
	parSiz := -total
      ELSE
	parSiz := total
      END;
    END GetActuals;

  END ActualParams;

(*==============================================================*)
(*==============================================================*)

    PROCEDURE FindOffsets(tree : IdTree;
		      VAR size : INTEGER);
    BEGIN
      (*
       *  Details of the stack mark are (stackInverted)
       *
       *	| second param    |  <--- [fp + frameSize + 4]
       *	| first parameter |  <--- [fp + frameSize]
       *	|-----------------|
       *	| saved inst ptr  |  <--- [fp + linkSize]
       * 	| old frame ptr   |  <--- fp points here
       *	|-----------------|
       *	| local vars here |  <--- [fp - size]
       *
       *  Details of the stack mark are (stackUpright)
       *
       *	| local vars here |  <--- [fp + linkSize]
       *	|-----------------|
       * 	| old frame ptr   |  <--- fp points here
       *	| saved inst ptr  |  <--- [fp - 4]
       *	|-----------------|
       *	| first parameter |  <--- [fp - adrSize - size]
       *	| second param    |  <--- [fp - adrSize - ... ]
       *
       *)
      IF tree <> NIL THEN 
	WITH tree^ DO
	  IF ident^.idClass = varNode THEN
	    IF ident^.varClass = auto THEN (* ==> local variable *)
	      IF stackInverted THEN
	      (*
	       *  because the variables grow downward, (the neg-
	       *  ative of the) stack offset is preincremented
	       *)
	        INC(size,ident^.varType^.size);
	        IF ident^.varType^.alignMask < 3C THEN	(* jl Jun 94 *)
	          Align(size,3C);  (* put locals on at least a quad-boundary *)
		ELSE
	          Align(size,ident^.varType^.alignMask);
		END;
	        (* and now set offset *)
	        ident^.varOffset := -size;
	      ELSE (* stack is upright *)
	        IF ident^.varType^.alignMask < 3C THEN
	          Align(size,3C);
		ELSE
	          Align(size,ident^.varType^.alignMask);
		END;
	        ident^.varOffset := size;
	        INC(size,ident^.varType^.size);
	      END;
	    END;
	  END;
	  FindOffsets(left,size);
	  FindOffsets(right,size);
	END; (* with *)
      END; (* if not empty *)
    END FindOffsets;

    PROCEDURE ParOffsets(proc : IdDesc;		(* the proc to process *)
		    VAR aSize : INTEGER);	(* the copy area size  *)
      VAR id   : IdDesc;
	  isX  : BOOLEAN;
	  curs : ElemPtr;
	  elem : FormalType;
	  size : INTEGER;
	  pOffset : INTEGER;
	  targetBig : BOOLEAN;

      PROCEDURE DoAllHighs(idd : IdDesc; off : INTEGER; inv : BOOLEAN);
      BEGIN
	INC(off,bytesInWord);
        idd := idd^.nextHigh;
	REPEAT
	  IF inv THEN idd^.varOffset := off ELSE idd^.varOffset := -off END;
	  idd := idd^.nextHigh;
	  INC(off,bytesInWord);
	UNTIL idd = NIL;
      END DoAllHighs;

    BEGIN
      aSize := 0;
      isX  := (proc^.idClass = externProc) AND 		(* protect *)
					proc^.module^.macro;
      targetBig := bigEndian <> crossEndian;
      (*
       *  If there is a destination pointer, then there
       *  is a dummy first param which points to this
       *
       *  Details of the stack mark are (stackInverted)
       *
       *	| second param    |  <--- [fp + frameSize + 4]
       *	| first parameter |  <--- [fp + frameSize]
       *	|-----------------|
       *	| saved inst ptr  |  <--- [fp + linkSize]
       * 	| old frame ptr   |  <--- fp points here
       *	|-----------------|
       *	| local vars here |  <--- [fp - size]
       *
       *  Details of the stack mark are (stackUpright)
       *
       *	| local vars here |  <--- [fp + linkSize]
       *	|-----------------|
       * 	| old frame ptr   |  <--- fp points here
       *	| saved inst ptr  |  <--- [fp - 4]
       *	|-----------------|
       *	| first parameter |  <--- [fp - adrSize - size]
       *	| second param    |  <--- [fp - adrSize - ... ]
       *)
(* stack mark size becomes zero with AP and LP pointers *)
      IF stackInverted THEN pOffset := stackMarkSize;
      ELSE pOffset := 0;
      END;
      IF NeedsDestPtr(proc^.procType) THEN INC(pOffset,adrSize) END;
      InitCursor(proc^.procType^.params,curs);
      WHILE NOT Ended(curs) DO
	(* params are always on min boundary *)
	GetNext(curs,elem);
(*
 *	Align(pOffset,elem^.type^.alignMask);
 *)
        CASE elem^.form OF
	| valForm :
	    IF IsRefParam(elem^.type) THEN			(* Oct 92 *)
	      (* ==> value object with a local copy *)
	      size := adrSize; (* passed by reference *)
	      IF IsCopyParam(elem^.type) THEN
		INC(aSize,elem^.type^.size);			(* copy size *)
		Align(aSize,paramMap[elem^.type^.alignMask]);
	      END;
	    ELSE 
	      Align(pOffset,paramMap[elem^.type^.alignMask]);
	      size := elem^.type^.size;
	    END;
	| varForm : 
	    size := bytesInWord;
	| openVarForm, openValForm :
	    size := adrSize + elem^.dimN * bytesInWord; (* ptr, high(s) *)
	END;
	LookupInThisScope(proc^.scope,elem^.fNam,id);
	Assert(id <> NIL);
	(* now place the offset *)
	IF stackInverted THEN
	 (*
	  *  adjust for bytes and halfwords being at
	  *  at the "wrong" end of the param word.
	  *)
	  IF (size < INT(bytesInWord)) AND targetBig THEN 
	    id^.varOffset := pOffset + INT(bytesInWord) - size;
	  ELSE
	    id^.varOffset := pOffset;
	  END;
	  IF (elem^.form = openValForm) OR
	     (elem^.form = openVarForm) THEN
	    DoAllHighs(id,pOffset,TRUE);
	  END;
	  INC(pOffset,size); (* post increment *)
	  Align(pOffset,paramMap[0C]);
	ELSE
	  INC(pOffset,size); (* pre- increment *)
	  Align(pOffset,paramMap[0C]);
	  id^.varOffset := -pOffset;
	  IF (elem^.form = openValForm) OR
	     (elem^.form = openVarForm) THEN
	    DoAllHighs(id,pOffset,FALSE);
	  END;
	END;
      END; (* while *)
(* stack mark size becomes zero with AP and LP pointers *)
      proc^.procType^.parSiz := pOffset - INT(stackMarkSize);
    END ParOffsets;

    PROCEDURE SetCurrentEnv(id : IdDesc);
      VAR total : INTEGER;
    BEGIN
      current := id;
      isMain  := id = thisCompileUnit;
      (*
       *  variable size is final tempSize
       *  tmpOffset is bottom of area and is aligned
       *)
      total := id^.body^.tempSize;
      Align(total,alignMap[8]);
      tmpOffset := -total;
(*
 *    IF stackInverted THEN tmpOffset := -total;
 *    ELSE tmpOffset := total;
 *    END;
 *)
      IF isMain THEN
        copyOffset := tmpOffset;
      ELSE
        INC(total,id^.body^.copySize);
        Align(total, alignMap[8]);
        copyOffset := -total;
(*
 *      IF stackInverted THEN copyOffset := -total;
 *      ELSE copyOffset := total;
 *      END;
 *)
      END;
    END SetCurrentEnv;

    PROCEDURE DoAllOffsets(id : IdDesc);
      VAR count : INTEGER;
	  copy  : INTEGER;
	  ok    : BOOLEAN;

    BEGIN
      dummy.idClass := unknown;
      (*
       *  now to find the local variable size
       *  and compute the offsets in the stack
       *)
(* stack mark size becomes zero with AP and LP pointers *)
      IF stackInverted THEN count := 0;
      ELSE (* stackUpright *) count := stackMarkSize;
      END;
      IF id = thisCompileUnit THEN 
      ELSE
        IF hasUplevObj IN id^.body^.callAttrib THEN
	  (*
	   *  make space for the display save
	   *)
	  INC(count,displayElSize);
        END;
	ParOffsets(id,copy);
        (*
	 *  now save information in StrucRec
	 *)
        id^.body^.copySize := copy;
	FindOffsets(id^.scope,count);
       (*
	*  here is a special marker to ensure that the
	*  anonymous result pointer gets a .LOCAL 
	*  reference. RISCs need this ...		(kjg Mar 93)
	*)
	IF NeedsDestPtr(id^.procType) THEN
	  M2NodeDefs.InsertRef(id^.scope,ADR(dummy),ok);
	END;
      END;
(*
 *    IF superVerbose IN modState THEN
 *      DiagName(id^.name);
 *	StdError.WriteLn;
 *	StdError.WriteString("tempSize=");
 *	StdError.WriteCard(id^.body^.tempSize,0);
 *	StdError.WriteLn;
 *	StdError.WriteString("varSize=");
 *	StdError.WriteCard(count,0);
 *	StdError.WriteLn;
 *	INC(id^.body^.tempSize,count);
 *	StdError.WriteString("frameSize=");
 *	StdError.WriteCard(id^.body^.tempSize,0);
 *	StdError.WriteLn;
 *	StdError.WriteString("copySize=");
 *	StdError.WriteCard(id^.body^.copySize,0);
 *	StdError.WriteLn;
 *    ELSE
 *)
	INC(id^.body^.tempSize,count);
(*
 *    END;
 *)
    END DoAllOffsets;

    PROCEDURE DoBaseOffsets();
      VAR count : INTEGER;
	  ident : IdDesc;
    BEGIN
(* stack mark size becomes zero with AP and LP pointers *)
      IF stackInverted THEN count := 0;
      ELSE (* stackUpright *) count := stackMarkSize;
      END;
      ident := thisCompileUnit;
      ident^.body^.copySize := 0;
      FindOffsets(ident^.scope,count);
      INC(ident^.body^.tempSize,count);
    END DoBaseOffsets;

    PROCEDURE StatLinkAttributes;
    (*
     *  does offsets for all procedures
     *)
      VAR curs : INTEGER;
	  elem : IdDesc;

    BEGIN
      FOR curs := 0 TO HIGH(codeBlkList) DO
	elem := codeBlkList[curs];
        IF elem^.idClass <> modNode THEN
	  DoAllOffsets(elem);
        END;
      END;
      DoBaseOffsets;
    END StatLinkAttributes;

END M2ProcState.
