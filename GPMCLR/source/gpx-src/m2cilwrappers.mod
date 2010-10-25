(****************************************************************)
(*                                                              *)
(*              Modula-2 Compiler Source Module                 *)
(*                                                              *)
(*    Emit Wrapper functions for String to Array conversions    *)
(*                                                              *)
(*    (c) copyright 2003 Faculty of Information Technology.     *)
(*                                                              *)
(*      original dcf module : kjg July 1996                     *)
(*      original cil module : kjg November 2003                 *)
(*      modifications       :                                   *)
(*                                                              *)
(****************************************************************)

IMPLEMENTATION MODULE M2CilWrappers;

  IMPORT SYSTEM;

  FROM VARSTRS IMPORT APPEND;
  FROM Storage IMPORT ALLOCATE, DEALLOCATE;

  FROM ProgArgs        IMPORT Assert;
  FROM M2TabInitialize IMPORT PointerTo;

  FROM M2NodeDefs    IMPORT 
        thisCompileUnit, MakeFormal, FormalClass,
        FormalType, TyNodeClass, CreateTypeDesc,
        CreateIdDesc, IdNodeClass, TypeDesc,
        IdDesc, IdRec, IdTree, IdString, TreeRec, InsertRef;

  FROM M2Designators IMPORT 
        InitDesignator,
        ExprDesc, ExprRec, ExprNodeClass, DesigRec, 
        ForceAccessMode, CreateExprDesc, AccessMode;

  FROM M2SSUtilities IMPORT LookupInThisScope;

  FROM M2Scanner IMPORT CurrentFlags;

  FROM M2CILwriter IMPORT
        wrapBkt, ClassBegin, ClassEnd, 
        cilEqFrm, cilEqTyp, lexLevel,
        WriteComment, CopyArg, WrapperCopy, CallTos,
        GenerateEntry, Return, GenerateExit;

  FROM M2Alphabets IMPORT 
        HashBucketType, Flags;

  FROM M2MachineConstants IMPORT 
        doubleSize, floatSize, stackMarkSize,
        bytesInWord, adrSize, paramMap, alignMap;

  FROM M2NameHandler IMPORT 
        EnterString, GetSourceRep, anonBkt;

  FROM GenSequenceSupport IMPORT
        Sequence, InitCursor, GetNext, Ended, 
        ElemPtr, InitSequence, LinkRight;

 (* ============================================= *)

  CONST init = "_$";
           (*   012  *)

  VAR   root : IdTree;  
        list : IdString;
        str  : ARRAY [0 .. 1023] OF CHAR;

 (* ============================================= *)

  PROCEDURE Append(ovl : IdDesc; elm : IdDesc);
  BEGIN
    LinkRight(ovl^.overloadList, elm);
    APPEND(list, elm);
  END Append;

 (* ============================================= *)

  PROCEDURE isCilEquiv(pTp, wTp : TypeDesc) : BOOLEAN;
    VAR lCrs, rCrs : ElemPtr;
        lElm, rElm : FormalType;
  BEGIN
    InitCursor(pTp^.params, lCrs);
    InitCursor(wTp^.params, rCrs);
    WHILE NOT Ended(lCrs) DO
      GetNext(lCrs, lElm);
      GetNext(rCrs, rElm);
      IF (rElm = NIL) OR NOT cilEqFrm(lElm, rElm) THEN RETURN FALSE END;
    END;
    IF NOT cilEqTyp(pTp^.result, wTp^.result) THEN RETURN FALSE END;
   (*
    *  Procedure formal list has finished. 
    *  Ok if wrapper formal list has just one element left.
    *)
    GetNext(rCrs, rElm);
    RETURN (rElm <> NIL) AND Ended(rCrs);
  END isCilEquiv;

 (* ============================================= *)

  PROCEDURE GetWrapperDesc(hsh : HashBucketType;
                           pTp : TypeDesc;
                       VAR out : IdDesc;
                       VAR pId : IdDesc);
    VAR ovLd : IdDesc;
        ovId : IdDesc;
        wrId : IdDesc;
        oCrs : ElemPtr;
        fCrs : ElemPtr;
        fElm : FormalType;
        ok   : BOOLEAN;
  BEGIN
   (*
    *  Find, or if necessary create an overload descriptor.
    *)
    wrId := NIL;
    LookupInThisScope(root, hsh, ovLd);
    IF ovLd = NIL THEN 
      CreateIdDesc(hsh, ovLd, overload);
      InitSequence(ovLd^.overloadList);
      InsertRef(root, ovLd, ok);
    ELSE
      Assert(ovLd^.idClass = overload);
     (*
      *   Try to find an existing, matching wrapper.
      *)
      InitCursor(ovLd^.overloadList, oCrs);
      WHILE NOT Ended(oCrs) AND (wrId = NIL) DO
        GetNext(oCrs, ovId); 
        IF isCilEquiv(pTp, ovId^.procType) THEN wrId := ovId END;
      END;
    END;
   (*
    *   If wrId not found then create a new one.
    *)
    IF wrId = NIL THEN
      CreateIdDesc(hsh, wrId, cilWrapper);
      CreateTypeDesc(thisCompileUnit, wrId^.procType, procTypes);
      wrId^.uphill := thisCompileUnit;
      wrId^.body   := NIL;        (* Actually, it is initally NIL anyway. *)
      InitCursor(pTp^.params, fCrs);
      WHILE NOT Ended(fCrs) DO
        GetNext(fCrs, fElm);
        LinkRight(wrId^.procType^.params, fElm);
      END;
      LinkRight(wrId^.procType^.params, 
                           MakeFormal(pTp, anonBkt, anonBkt, valForm, 0));
      wrId^.procType^.result := pTp^.result;
      Append(ovLd, wrId);
    END;
    out := ovLd;
    pId := wrId;
  END GetWrapperDesc;

 (* ============================================= *
  *  In the namestring, the following code applies
  *         s ==> a string which needs to be copied
  *         o ==> an open array parameter
  *         h ==> a high value
  *         x ==> anything else
  *         l ==> the static link
  *         v ==> the procedure variable
  * ============================================= *)

  PROCEDURE MkWrap(VAR desig : DesigRec;   (* procedure identifier *)
                   VAR acSeq : Sequence;   (* actual param list    *)
                       exTyp : TypeDesc;   (* procedure typeDesc   *)
                       thisP : IdDesc);    (* current procDesc     *)
    VAR new : IdDesc;                 (* new ident descriptor      *)
        ovl : IdDesc;                 (* the overload descriptor   *)
        iOk : BOOLEAN;
        idx : CARDINAL;
        hix : CARDINAL;
        lxLv : CARDINAL;
        trgt : IdDesc;
        aCrs : ElemPtr;
        fCrs : ElemPtr;
        aElm : ExprDesc;
        xPar : ExprDesc;        (* the additional proc-param *)
        fElm : FormalType;
        nSeq : Sequence;        (* new actual param sequence *)
        hNam : HashBucketType;
        size : CARDINAL;

  BEGIN
   (* 
    *  Too dangerous to attempt this if semantic
    *  errors have been detected in param passing.
    *)
    IF semErrors IN CurrentFlags() THEN RETURN END;
    idx := LENGTH(init);
    str := init;
    trgt := desig.variable;
    lxLv := 1;
   (* 
    *   Check if desig denotes a procNode of a nested procedure?
    *)
    IF trgt^.idClass # varNode THEN lxLv := lexLevel(trgt) END;

    InitSequence(nSeq);
    InitCursor(acSeq,aCrs);
    InitCursor(exTyp^.params,fCrs);
   (* 
    *   Check if desig denotes a procNode of a nested procedure?
    *)
    IF lxLv > 1 THEN
      str[idx] := "l"; INC(idx);
      str[idx] := CHR(ORD("0") + lxLv MOD 8); INC(idx);
      str[idx] := CHR(ORD("0") + lxLv DIV 8); INC(idx);
    END;

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
        ELSE
          str[idx] := "o";
        END;
        INC(idx); 
        FOR hix := 1 TO fElm^.dimN DO
          str[idx] := "h"; INC(idx); 
          GetNext(aCrs,aElm);                 (* skip high descs *)
          LinkRight(nSeq,aElm);
        END;
      ELSE
        str[idx] := "x"; INC(idx);
      END;
    END;
    str[idx] := "v"; INC(idx);
    str[idx] := ""; 
    EnterString(str, hNam);
   (*
    *  Create an expression which calls proc
    *  and append this as an extra actual param.
    *)
    CreateExprDesc(xPar, desigNode);
    xPar^.name := desig;
    LinkRight(acSeq, xPar);
   (*
    *  Now get, or if necessary create a wrapper descriptor.
    *)
    GetWrapperDesc(hNam, exTyp, ovl, new);
    xPar^.exprType := new^.procType;
   (*
    *   Copying the uphill pointer fools the code generator
    *   into thinking the *wrapper* is a nested procedure 
    *   in the *target* is a nested procedure.
    *)
    IF lxLv > 1 THEN new^.uphill := trgt^.uphill END;
   (*
    *  This is (now) an existing wrapper, so just fix
    *  up the call, by appending the extra param
    *)
    InitDesignator(desig);
    desig.variable := new;
    ForceAccessMode(desig, directNonL);
  END MkWrap;
                
 (* ============================================= *
  *  Write out all of the procedure wrappers, by
  *  traversing the IdString vector "list".
  *)
  PROCEDURE WriteWrappers();

   (* ============================================= *
    *  In the namestring, the following code applies
    *         s ==> a string which needs to be copied
    *         o ==> open array, without string actual
    *         x ==> any other parameter
    *         h ==> a high value
    *         l ==> the static link
    *         v ==> the procedure variable
    * ============================================= *)

    PROCEDURE Wrapper(id : IdDesc);
      VAR idx : CARDINAL;
          max : CARDINAL;
          num : CARDINAL;        (* number of params to procvar  *)
          nst : BOOLEAN;         (* is target a nested procedure *)
          fnc : BOOLEAN;         (* target proc returns a value  *)
          chr : CHAR;
          fCrs : ElemPtr;
          form : FormalType;
    BEGIN
      GenerateEntry(id);

      max := 0;
      num := 0;
      nst := FALSE;

      idx := LENGTH(init);
      GetSourceRep(id^.name,str,max);
      IF str[idx] = "l" THEN 
        INC(idx, 3); INC(num); nst := TRUE;
      END;  (* skip lex level *)

      InitCursor(id^.procType^.params,fCrs);
     (*
      *   Expand the stack, and copy string blobs.
      *   This must be done in a separate loop, since
      *   the execution of "localloc" is only valid
      *   if the evaluation stack is empty.
      *)
      WHILE NOT Ended(fCrs) DO
        GetNext(fCrs,form);
        CASE str[idx] OF
        | "o" : INC(idx); INC(num);
                WHILE str[idx] = "h" DO INC(idx); INC(num) END;
        | "s" : (* Expand stack frame by buffer size *)
                WriteComment("expand frame and copy value arg");
                WrapperCopy(num, form^.type^.size);
                INC(idx); INC(num);
                (* Skip the size data *)
                WHILE str[idx] <> "h" DO INC(idx) END;
                (* Count the (single) high value *)
                INC(idx); INC(num);
        ELSE    
                INC(idx); INC(num);
        END;
      END;
     (*
      *   Now copy the args to the outgoing calli.
      *)
      num := 0;
      idx := LENGTH(init);
      WriteComment("copy incoming to outgoing args");
      WHILE idx < max DO
        chr := str[idx];
        CopyArg(num); INC(idx); INC(num);
       (*
        *  Now deal with the HIGH values.
        *)
        IF chr = "o" THEN
          WHILE str[idx] = "h" DO CopyArg(num); INC(idx); INC(num) END;
        ELSIF chr = "s" THEN
          WHILE str[idx] <> "h" DO INC(idx) END;
          CopyArg(num); INC(idx); INC(num);
        ELSIF chr = "l" THEN 
          INC(idx, 2);
        END;
      END;
     (*
      *   Call the procedure variable;
      *)
      fnc := form^.type^.result # NIL;
      CallTos(form^.type, num-1, ORD(fnc), nst);
      Return;
      GenerateExit(id);
    END Wrapper;

    VAR jdx : INTEGER;

  BEGIN
    IF HIGH(list) >= 0 THEN
      ClassBegin(wrapBkt);
      FOR jdx := 0 TO HIGH(list) DO
        Wrapper(list[jdx]);
      END;
      ClassEnd(wrapBkt);
    END;
  END WriteWrappers;
 (* ============================================= *)

BEGIN
  root := NIL;
  NEW(list, 8);
END M2CilWrappers.
