(****************************************************************)
(*                                                              *)
(*              Modula-2 Compiler Source Module                 *)
(*                                                              *)
(*    Emit Wrapper functions for String to Array conversions    *)
(*                                                              *)
(*    (c) copyright 1996 Faculty of Information Technology.     *)
(*                                                              *)
(*      original module : kjg July 1996                         *)
(*      modifications   :                                       *)
(*                                                              *)
(****************************************************************
$Log: m2wrappe.mod,v $
Revision 1.9  1997/01/16 05:32:56  gough
MakeFormal now has a changed parameter list.

Revision 1.8  1996/09/05 11:15:21  lederman
$ characters illegal in procedure names on RS6000 so go for __wrap instead

Revision 1.7  1996/09/04 07:28:46  lederman
check for pointer types before real types so pointers to reals work

Revision 1.6  1996/08/29 03:11:20  gough
ensure that size of elment is used in name of wrapper procedures.
alignment must also be used for safety.

Revision 1.3  1996/08/07 23:45:44  gough
fix up bad dcode for mkDstP -- incorrect for SPARC

Revision 1.2  1996/08/07 07:27:21  gough
ensure that OPENCOPY declaration precede all LOCAL declarations.

Revision 1.1  1996/08/06 23:46:26  gough
Initial revision
*****************************************************************)

IMPLEMENTATION MODULE M2DcfWrappers;

  IMPORT SYSTEM;

  FROM ProgArgs  IMPORT Assert;

  FROM M2NodeDefs    IMPORT 
	thisCompileUnit, MakeFormal, FormalClass,
	FormalType, TyNodeClass, CreateTypeDesc,
	CreateIdDesc, IdNodeClass, TypeDesc,
	IdDesc, IdRec, IdTree, TreeRec, InsertRef;

  FROM M2Designators IMPORT 
	InitDesignator,
	ExprDesc, ExprRec, ExprNodeClass, DesigRec, 
	ForceAccessMode, CreateExprDesc, AccessMode;

  FROM M2SSUtilities IMPORT 
	LookupInThisScope;

  FROM M2Scanner IMPORT 
	CurrentFlags;

  FROM M2ProcState IMPORT 
	NeedsDestPtr, IsRefParam;

  FROM M2Alphabets IMPORT 
	HashBucketType, Flags;

  FROM M2MachineConstants IMPORT 
	doubleSize, floatSize, stackMarkSize,
	bytesInWord, adrSize, paramMap, alignMap;

  FROM M2NameHandler IMPORT 
	EnterString, GetSourceRep, anonBkt;

  FROM M2InOut IMPORT 
	WriteObjByte;

  FROM GenSequenceSupport IMPORT
	Sequence, InitCursor, GetNext, Ended, 
	ElemPtr, InitSequence, LinkRight;

 (* ============================================= *)

  CONST init = "__wrap_";
	     (* 0123456 *)
	eol  = 12C;

  VAR	root : IdTree;  

 (* ============================================= *)
  PROCEDURE WStr(s : ARRAY OF CHAR);
    VAR i : CARDINAL;
  BEGIN
    FOR i := 0 TO HIGH(s) DO
      IF s[i] = "" THEN RETURN END;
      WriteObjByte(s[i]);
    END;
  END WStr;

  PROCEDURE WCrd(n : CARDINAL);
  BEGIN
    IF n > 9 THEN WCrd(n DIV 10) END;
    WriteObjByte(CHR(ORD("0") + n MOD 10));
  END WCrd;

  PROCEDURE WriteExit(rTp : TypeDesc);
  BEGIN
    IF rTp <> NIL THEN
      IF rTp^.tyClass = doubles THEN
	WStr("	pshRetD" + eol + "	popRetD" + eol);
      ELSIF rTp^.tyClass = floats THEN
	WStr("	pshRetF" + eol + "	popRetF" + eol);
      ELSE
	WStr("	pshRetW" + eol + "	popRetW" + eol);
      END;
    END;
    WStr("	exit" + eol + "	endP" + eol + ".ENDP" + eol + eol);
  END WriteExit;

  PROCEDURE WriteEntry;
  BEGIN
    WStr(".ENTRY" + eol);
  END WriteEntry;

  PROCEDURE WriteHeader(VAR str : ARRAY OF CHAR; siz : CARDINAL);
  BEGIN
    WriteObjByte(eol);
    WStr(".PROC _"); WStr(str);
    WStr("(.NOCHECK, .SIZE=0, .NODISPLAY, .ASSEMBLY=");
    WCrd(siz); WriteObjByte(")"); WriteObjByte(eol);
  END WriteHeader;

  PROCEDURE DecLocal(off : CARDINAL; siz : CARDINAL; isF : BOOLEAN);
  BEGIN
    WStr("  .LOCAL __"); WCrd(off); WStr("__ "); WCrd(off + stackMarkSize);
    WriteObjByte(","); WCrd(siz); WStr(" (0,0,0)");
    IF isF THEN WStr(" fpParam") END;
    WriteObjByte(eol);
  END DecLocal;

  PROCEDURE DecOpenCopy(off : CARDINAL; typ : TypeDesc);
  BEGIN
    WStr("  .OPENCOPY "); WCrd(off + stackMarkSize);
    WStr(" .SIZE "); WCrd(typ^.size);
    WStr(" .ALIGN "); WCrd(ORD(typ^.alignMask) + 1);
    WriteObjByte(eol);
  END DecOpenCopy;

  PROCEDURE CopyResPtr(siz : CARDINAL);
  BEGIN
    WStr("	pshDstP" + eol + "	mkDstP	"); WCrd(siz);
    WriteObjByte(eol);
  END CopyResPtr;

  PROCEDURE CallProcVar(off, num : CARDINAL);
  BEGIN
    WStr("	pshAP	"); WCrd(off); WriteObjByte(eol);
    WStr("	derefW" + eol + "	popCall	"); WCrd(num);
    WriteObjByte(eol);
  END CallProcVar;

  PROCEDURE CopyParam(off : INTEGER; siz : CARDINAL; isF : BOOLEAN);
  BEGIN
    WStr("	pshAP	"); WCrd(off); WriteObjByte(eol);
    WStr("	deref"); 
    IF isF THEN
      IF siz = floatSize THEN WriteObjByte("F") ELSE WriteObjByte("D") END;
    ELSE
      WriteObjByte("W");
    END;
    WriteObjByte(eol);
    WStr("	mkPar	"); WCrd(siz); WriteObjByte(","); WCrd(off);
    IF isF THEN WStr(" fpParam") END;
    WriteObjByte(eol);
  END CopyParam;

 (* ============================================= *)

 (* ============================================= *
  *  In the namestring, the following code applies
  * 	s ==> a string which needs to be copied
  * 	p ==> a reference parameter
  * 	r ==> return ptr in dedicated location
  * 	d ==> an fp double parameter
  * 	f ==> an fp single parameter
  * 	h ==> a high value
  * 	w ==> a word parameter
  * 	v ==> the procedure variable
  * 	_ ==> an alignment pad
  * ============================================= *)

  PROCEDURE MkWrap(VAR desig : DesigRec;   (* procedure identifier *)
		   VAR acSeq : Sequence;   (* actual param list    *)
		       exTyp : TypeDesc;   (* procedure typeDesc   *)
		       thisP : IdDesc);	   (* current procDesc     *)
    VAR new : IdDesc;		(* new ident descriptor      *)
	iOk : BOOLEAN;
	siz : INTEGER;		(* parameter size of wrapper *)
	max : INTEGER;
	idx : CARDINAL;
	hix : CARDINAL;
	str : ARRAY [0 .. 1023] OF CHAR;
	ofst : INTEGER;
	aCrs : ElemPtr;
	fCrs : ElemPtr;
	aElm : ExprDesc;
	xPar : ExprDesc;	(* the additional proc-param *)
	fElm : FormalType;
	nSeq : Sequence;	(* new actual param sequence *)
	hNam : HashBucketType;
	size : CARDINAL;

    PROCEDURE Align(VAR offset : INTEGER; align : CHAR);
      VAR set : BITSET;
    BEGIN
      set := SYSTEM.CAST(BITSET,offset) * SYSTEM.CAST(BITSET,align);
      IF set <> BITSET{} THEN
	str[idx] := "_"; INC(idx); INC(offset,bytesInWord);
      END;
    END Align;

  BEGIN
   (* assume at least word-sized alignment *)
    Assert(paramMap[0C] >= alignMap[adrSize], "Wrappers need finer par-align");
   (* 
    *  Too dangerous to attempt this if semantic
    *  errors have been detected in param passing.
    *)
    IF semErrors IN CurrentFlags() THEN RETURN END;
    idx := LENGTH(init);
    str := init;
    ofst := 0;
    IF (exTyp^.result <> NIL) AND
	((exTyp^.result^.tyClass = arrays) OR
	 (exTyp^.result^.tyClass = records) OR
	 ((exTyp^.result^.tyClass = sets) AND 
	  (exTyp^.result^.size > bytesInWord))) THEN (* needs return pointer *)
      IF NeedsDestPtr(exTyp) THEN 		  (* ptr is extra param   *)
	str[idx] := "p";INC(ofst,adrSize);
      ELSE
	str[idx] := "r";
      END;
      INC(idx);
    END;
    InitSequence(nSeq);
    InitCursor(acSeq,aCrs);
    InitCursor(exTyp^.params,fCrs);
    WHILE NOT Ended(fCrs) AND NOT Ended(aCrs) DO
      GetNext(aCrs,aElm); LinkRight(nSeq,aElm);
      GetNext(fCrs,fElm); 
      IF fElm^.form >= openValForm THEN
	IF (fElm^.form = openValForm) AND
	   (aElm^.exprType^.tyClass = stringTs) THEN
	  str[idx] := "s"; 
	  size := fElm^.type^.size;
	  WHILE size > 0 DO
	    INC(idx); 
	    str[idx] := CHR(ORD("0") + size MOD 8); 
	    size := size DIV 8;
	  END;
	  INC(idx); str[idx] := CHR(ORD("0") + ORD(fElm^.type^.alignMask));
	ELSE
	  str[idx] := "o";
	END;
	INC(idx); INC(ofst,bytesInWord);
	FOR hix := 1 TO fElm^.dimN DO
	  str[idx] := "h"; INC(idx); INC(ofst,bytesInWord);
	  GetNext(aCrs,aElm); 		(* skip high descs *)
	  LinkRight(nSeq,aElm);
	END;
      ELSIF (fElm^.form <> valForm) OR IsRefParam(fElm^.type) THEN
	str[idx] := "p"; INC(idx); INC(ofst,adrSize);
      ELSIF aElm^.exprType^.tyClass = doubles THEN
	Align(ofst,paramMap[fElm^.type^.alignMask]);
	str[idx] := "d"; INC(idx); INC(ofst,doubleSize);
      ELSIF aElm^.exprType^.tyClass = floats THEN
	Align(ofst,paramMap[fElm^.type^.alignMask]);
	str[idx] := "f"; INC(idx); INC(ofst,floatSize);
      ELSE
	Align(ofst,paramMap[fElm^.type^.alignMask]);
	max := ofst; INC(max,fElm^.type^.size);
	WHILE ofst < max DO
	  str[idx] := "w"; INC(idx); INC(ofst,bytesInWord);
	END;
      END;
    END;
    str[idx] := "v"; INC(idx);
    str[idx] := ""; 
    EnterString(str,hNam);
    siz := exTyp^.parSiz + INT(bytesInWord);
    IF siz > thisP^.body^.maxParSize THEN thisP^.body^.maxParSize := siz END;
   (*
    *  Create an expression which calls proc
    *  and append this as an extra actual param.
    *)
    CreateExprDesc(xPar,desigNode);
    xPar^.name := desig;
    LinkRight(acSeq,xPar);
   (*
    *  Now check if this is a new wrapper.
    *)
    LookupInThisScope(root,hNam,new);
    IF new = NIL THEN
      CreateIdDesc(hNam,new,procNode);
      CreateTypeDesc(thisCompileUnit,new^.procType,procTypes);
      InitCursor(exTyp^.params,fCrs);
      WHILE NOT Ended(fCrs) DO
	GetNext(fCrs,fElm);
	LinkRight(new^.procType^.params,fElm);
      END;
      LinkRight(new^.procType^.params,
			MakeFormal(new^.procType,anonBkt,anonBkt,valForm,0));
      new^.procType^.result := exTyp^.result;
      new^.procType^.parSiz := siz;
      InsertRef(root,new,iOk);
    END;
    xPar^.exprType := new^.procType;
   (*
    *  This is an existing wrapper, so just fix
    *  up the call, by appending the extra param
    *)
    InitDesignator(desig);
    desig.variable := new;
    ForceAccessMode(desig,directNonL);
  END MkWrap;
		
 (* ============================================= *
  *  Write out all of the procedure wrappers, by
  *  recursively traversing the identifier tree.
  *)
  PROCEDURE WriteWrappers();

   (* ============================================= *
    *  In the namestring, the following code applies
    * 	s ==> a string which needs to be copied
    * 	o ==> open array, without string actual
    * 	p ==> a reference parameter
    * 	r ==> return ptr in dedicated location
    * 	d ==> an fp double parameter
    * 	f ==> an fp single parameter
    * 	h ==> a high value
    * 	w ==> a word parameter
    * 	v ==> the procedure variable
    * 	_ ==> an alignment pad
    * ============================================= *)

    PROCEDURE Wrapper(id : IdDesc);
      VAR str : ARRAY [0 .. 1023] OF CHAR;
	  idx : CARDINAL;
	  max : CARDINAL;
	  siz : CARDINAL;	(* size of the returned value  *)
	  num : CARDINAL;	(* number of params to procvar *)
	  oft : INTEGER;
	  fCrs : ElemPtr;
	  form : FormalType;
    BEGIN
      max := 0;
      num := 0;
      oft := 0;
      idx := LENGTH(init);
      GetSourceRep(id^.name,str,max);
      WriteHeader(str,id^.procType^.parSiz);
      InitCursor(id^.procType^.params,fCrs);
      WHILE NOT Ended(fCrs) DO
        GetNext(fCrs,form);
	CASE str[idx] OF
	| "_" : INC(oft,bytesInWord);	INC(idx);
	| "d" : INC(oft,doubleSize);	INC(idx); INC(num);
	| "f" : INC(oft,floatSize);	INC(idx); INC(num);
	| "p", "v" : INC(oft,adrSize);	INC(idx); INC(num);
	| "r" : siz := form^.type^.size;INC(idx);
	| "o" : INC(oft,adrSize);	INC(idx); INC(num);
		WHILE str[idx] = "h" DO
		  INC(oft,bytesInWord);	INC(idx); INC(num);
		END;
	| "s" : DecOpenCopy(oft,form^.type);
		INC(oft,adrSize);	INC(idx); INC(num);
		WHILE str[idx] <> "h" DO INC(idx) END; (* skip size *)
		INC(oft,bytesInWord);	INC(idx); INC(num);
	| "w" : INC(oft,bytesInWord);	INC(idx); INC(num);
	END;
      END;
      oft := 0;
      FOR idx := LENGTH(init) TO max-1 DO
	CASE str[idx] OF
	| "_" : INC(oft,bytesInWord);
	| "d" : DecLocal(oft,doubleSize,TRUE);
		INC(oft,doubleSize);
	| "f" : DecLocal(oft,floatSize,TRUE);
		INC(oft,floatSize);
	| "p", "v", "o", "s" : 
		DecLocal(oft,adrSize,FALSE);
		INC(oft,adrSize);
	| "r" : (* skip *)
	| "h", "w" :	
		DecLocal(oft,bytesInWord,FALSE);
		INC(oft,bytesInWord);
	| '0' .. '7' : (* nothing *)
	END;
      END;
      WriteEntry;
      oft := 0;
      FOR idx := LENGTH(init) TO max-1 DO
	CASE str[idx] OF
	| "_" : INC(oft,bytesInWord);
	| "d" : CopyParam(oft,doubleSize,TRUE);
		INC(oft,doubleSize);
	| "f" : CopyParam(oft,floatSize,TRUE);
		INC(oft,floatSize);
	| "p","o","s" : 
		CopyParam(oft,adrSize,FALSE);
		INC(oft,adrSize);
	| "w","h" : 
		CopyParam(oft,bytesInWord,FALSE);
		INC(oft,bytesInWord);
	| "r" : CopyResPtr(siz);
	| "v" : CallProcVar(oft,num-1);
		INC(oft,adrSize);
	| '0' .. '7' : (* nothing *)
	END;
      END;
      WriteExit(id^.procType^.result);
    END Wrapper;

    PROCEDURE WriteWrapper(tree : IdTree);
    BEGIN
      IF tree <> NIL THEN
	Wrapper(tree^.ident);		(* write out this wrapper *)
	WriteWrapper(tree^.left);	(* recurse on left tree   *)
	WriteWrapper(tree^.right);	(* recurse on right tree  *)
      END;
    END WriteWrapper;

  BEGIN
    WriteWrapper(root);
  END WriteWrappers;
 (* ============================================= *)

BEGIN
  root := NIL;
END M2DcfWrappers.
