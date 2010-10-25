
(****************************************************************)
(*                                                              *)
(*              Modula-2 Compiler Source Module                 *)
(*                                                              *)
(*                Symbol Table Initialization                   *)
(*                                                              *)
(*     (c) copyright 1988 Faculty of Information Technology     *)
(*                                                              *)
(*      original module : kjg february 1988                     *)
(*      modifications   :                                       *)
(*      last modified   : 10-Mar-88                             *)
(*			:  8-Sep-90 updated to use alignMap     *)
(*			: 26-Mar-92 $ on ZZ,RR,S1,SS names	*)
(*			: 30-Mar-93 add ADDADR,SUBADR to names  *)
(*                                                              *)
(****************************************************************
$Log: m2tabini.mod,v $
Revision 1.7  1997/01/16 05:23:25  gough
        new procedure ExclStrExt which excludes string procPs.
        New procs PreconIdDesc, AssertIdDesc returning IdDescs.

Revision 1.6  1996/08/07 23:44:35  gough
VARSTRS.CUT name is defined

Revision 1.5  1996/07/30 00:03:09  gough
initialize APPEND and CONCAT in module VARSTRS

Revision 1.4  1995/10/10 23:56:32  lederman
DCode V3 HugeInt stuff

# Revision 1.3  1995/03/14  01:55:19  gough
# Initialize elementType of SS and S1 type descriptors to CHAR
#
# Revision 1.2  1994/11/15  04:36:18  gough
# initial InsertType initializes gdb type number fields from M2GdbSupport
#
# Revision 1.1  1994/04/07  05:27:15  lederman
# Initial revision
#
*****************************************************************
Revision 1.2  94/02/17  08:29:02  gough
fix up address so it is defined as pointer to byte
*****************************************************************)

IMPLEMENTATION MODULE M2TabInitialize;

IMPORT StdError;
IMPORT M2InOut;
FROM M2NodeDefs IMPORT 
           (* types for IdentTrees *)
        IdTree, TreeRec, InsertRef,
           (* types for identifier descriptors *)
        IdDesc, IdRec, IdNodeClass, StandardProcs, CreateIdDesc,
           (* types for type descriptors *)
        TypeDesc, TypeRec, TyNodeClass, CreateTypeDesc,
           (* global data structures *)
        globalModList, pervasiveUnit; 

FROM ProgArgs    IMPORT Assert;
FROM GenSequenceSupport IMPORT 
        Sequence, LinkLeft, LinkRight, ElemPtr, InitSequence;

FROM M2NameHandler IMPORT EnterString, stdBkt, sysBkt, anonBkt;
FROM M2Alphabets IMPORT HashBucketType;
FROM M2MachineConstants IMPORT bitsInWord, bytesInWord, bytesInReal,
	alignMap,
        byteSize, wordSize, floatSize, doubleSize, adrSize;

FROM M2GdbSupport IMPORT
	m2_int, c_char, m2_crd, m2_bool, c_void, c_vstar, ieeeFlt, 
	ieeeDbl, m2_proc, m2_char, m2_byte, m2_word, m2_set, m2_adr;

  VAR  pScope : IdTree;
       iPtr   : IdDesc;
       cstPtr : IdDesc; (* ptr to CAST IdRec *)
       assrtP : IdDesc; (* ptr to Assert IdRec *)
       precnP : IdDesc; (* ptr to Precon IdRec *)
       strMod : IdDesc;
  VAR  stdTp   : ARRAY TyNodeClass OF TypeDesc;

  PROCEDURE Initialize;
  (* precondition  : Reserved words have already been entered
                     in the table.
     postcondition : Standard objects are entered in the table,
                     and inserted in the IdentTree belonging
                     to the IdDesc pervasiveUnit.
                     SYSTEM ojects are inserted in the IdentTree
                     belonging to the IdentRec at head of the
                     globalModList.                              *)

      VAR  mod,
	   pMod : IdDesc;  (* pMod is pervasive mod IdDesc *)

      PROCEDURE InsertType(str : ARRAY OF CHAR;
                           siz : CARDINAL;
                           cls : TyNodeClass;
			   num : CARDINAL);
        VAR ptr : IdDesc;
            hsh : HashBucketType;
            ok  : BOOLEAN;
      BEGIN
        EnterString(str,hsh); (* insert in hash table *)
        CreateIdDesc(hsh,ptr,typeNode);
        WITH ptr^ DO
          CreateTypeDesc(mod,typType,cls);
          WITH typType^ DO
            tyName  := hsh;
            dumped  := TRUE;
            size    := siz;
	    tyNumber := num;
            IF siz = 0 THEN 
	      alignMask := 0C;
	      Assert((cls = S1) OR (cls = SS));
	      elementType := PointerTo(chars);
(*
 *  for RISC machines, the following line is correct
 *  however for M68K machines only even alignment is required
 *
 *          ELSE alignMask := CHR(siz - 1);
 *)
	    ELSE alignMask := alignMap[siz];
            END;
          END;
          stdTp[cls] := typType;
        END;
        InsertRef(pScope,ptr,ok);
      END InsertType;

      PROCEDURE InsertAlias(nam : ARRAY OF CHAR; ty : TypeDesc);
	VAR hsh : HashBucketType; ptr : IdDesc; ok : BOOLEAN;
      BEGIN
        EnterString(nam,hsh); (* insert in hash table *)
        CreateIdDesc(hsh,ptr,typeNode);
	ptr^.typType := ty;
	InsertRef(pScope,ptr,ok);
      END InsertAlias;

      PROCEDURE InsertBitset;
        VAR sPtr, bPtr : IdDesc;
            sHsh, bHsh : HashBucketType;
            ok  : BOOLEAN;
      BEGIN
        EnterString("BITSET",sHsh); (* insert in hash table *)
	EnterString("BIN",bHsh);
        CreateIdDesc(sHsh,sPtr,typeNode);
        CreateIdDesc(bHsh,bPtr,typeNode);
        CreateTypeDesc(pMod,sPtr^.typType,sets); (* parent is perv. scope *)
        CreateTypeDesc(mod,bPtr^.typType,subranges);
        WITH bPtr^.typType^ DO (* desc. for "BIN" *)
          dumped  := TRUE;
          tyName  := bHsh;
          size    := wordSize;
          alignMask := alignMap[bytesInWord];
          hostType := stdTp[cards];
          minRange := 0; maxRange := bitsInWord - 1;
	END; (* with *)
        WITH sPtr^.typType^ DO (* desc. for "BITSET" *)
          dumped  := TRUE;
          tyName  := sHsh;
          size    := bytesInWord;
	  tyNumber := 14;
          alignMask := alignMap[bytesInWord];
	  baseType := bPtr^.typType;
	END;
        stdTp[sets] := sPtr^.typType;
        InsertRef(pervasiveUnit^.scope,sPtr,ok);
        InsertRef(pScope,bPtr,ok); (* current is system scope *)
      END InsertBitset;

      PROCEDURE InsertStdProc(str : ARRAY OF CHAR;
                              ord : StandardProcs;
                              tag : IdNodeClass);
        VAR hsh : HashBucketType;
            ptr : IdDesc;
            ok  : BOOLEAN;
      BEGIN
        EnterString(str,hsh); (* insert in hash table *)
        CreateIdDesc(hsh,ptr,tag);
        ptr^.procVal := ord;
        InsertRef(pScope,ptr,ok);
      END InsertStdProc;

      PROCEDURE InsertCastProc();
        VAR hsh : HashBucketType;
            ok  : BOOLEAN;
      BEGIN
        EnterString("CAST",hsh); (* insert in hash table *)
        CreateIdDesc(hsh,cstPtr,stFunc);
        cstPtr^.procVal := castP;
        InsertRef(pScope,cstPtr,ok);
      END InsertCastProc;

      PROCEDURE InsertAssertProc();
        VAR hsh : HashBucketType;
            ok  : BOOLEAN;
      BEGIN
        EnterString("Assert",hsh); (* insert in hash table *)
        CreateIdDesc(hsh,assrtP,stProc);
        InsertRef(pScope,assrtP,ok);
        assrtP^.procVal := assertP;

        EnterString("$precon$",hsh); (* insert in hash table *)
        CreateIdDesc(hsh,precnP,stProc);
        InsertRef(pScope,precnP,ok);
        precnP^.procVal := preconP;

      END InsertAssertProc;

      PROCEDURE InsertStdCon(str : ARRAY OF CHAR;
                             val : CARDINAL;
                             typ : TypeDesc);
        VAR hsh : HashBucketType;
            ptr : IdDesc;
            ok  : BOOLEAN;
      BEGIN
        EnterString(str,hsh); (* insert in hash table *)
        CreateIdDesc(hsh,ptr,constNode);
        WITH ptr^ DO
          conType := typ;
          conValue.fixValue := val;
        END;
        InsertRef(pScope,ptr,ok);
      END InsertStdCon;

      PROCEDURE MakeSystemModule(hsh : HashBucketType; 
			     VAR ptr : IdDesc);
      BEGIN
	CreateIdDesc(hsh,ptr,exportNode);
	LinkRight(globalModList,ptr);
        ptr^.system := TRUE;
      END MakeSystemModule;

    VAR hsh : HashBucketType;

  BEGIN (* Initialize *)
    (* first, the standard identifiers *)
    CreateIdDesc(stdBkt,mod,modNode);
    pervasiveUnit := mod; mod^.frame := NIL;
    pScope := NIL; (* empty scope tree *)
    InsertType('CHAR',byteSize,chars,m2_char);
    InsertType('INTEGER',wordSize,ints,m2_int);
    InsertType('CARDINAL',wordSize,cards,m2_crd);
    InsertType('REAL',doubleSize,doubles,ieeeDbl);
    InsertAlias('LONGREAL',stdTp[doubles]);
    InsertType('SHORTREAL',floatSize,floats,ieeeFlt);
    InsertType('BOOLEAN',byteSize,bools,m2_bool);
    InsertStdCon('TRUE',1,stdTp[bools]);
    InsertStdCon('FALSE',0,stdTp[bools]);
    InsertType('$ZZ-',wordSize,II,m2_int);
    InsertType('$ZZ+',wordSize,UU,m2_crd);
    InsertType('$ZZ',wordSize,ZZ,m2_int);
    InsertType('$RR',doubleSize,RR,ieeeDbl);
    InsertType('PROC',adrSize,procTypes,m2_proc);
    InsertType('$S1',0,S1,c_char);
    InsertType('$SS',0,SS,c_vstar);
    (* only constants, length is held in the LexAttType *)
    InsertStdProc('ABS',absP,stFunc);
    InsertStdProc('CAP',capP,stFunc);
    InsertStdProc('CHR',chrP,stFunc);
    InsertStdProc('FLOAT',floatP,stFunc);
    InsertStdProc('LFLOAT',lfloatP,stFunc);
    InsertStdProc('SFLOAT',sfloatP,stFunc);
    InsertStdProc('HIGH',highP,stFunc);
    InsertStdProc('MIN',minP,stFunc);
    InsertStdProc('MAX',maxP,stFunc);
    InsertStdProc('ODD',oddP,stFunc);
    InsertStdProc('ORD',ordP,stFunc);
    InsertStdProc('TRUNC',truncP,stFunc);
    InsertStdProc('VAL',valP,stFunc);
    InsertStdProc('INT',intP,stFunc);
    InsertStdProc('SIZE',sizeP,stFunc);
    InsertStdProc('LENGTH',lengthP,stFunc);
    InsertStdProc('DEC',decP,stProc);
    InsertStdProc('EXCL',exclP,stProc);
    InsertStdProc('ABORT',abortP,stProc);
    InsertStdProc('HALT',haltP,stProc);
    InsertStdProc('INC',incP,stProc);
    InsertStdProc('INCL',inclP,stProc);
    InsertStdProc('NEW',newP,stProc);
    InsertStdProc('DISPOSE',disP,stProc);
    mod^.scope := pScope;
    (*
     *  the following assignment ensures that pMod
     *  continues to designate the pervasive scope
     *)
    pMod := mod;

    (* now for SYSTEM *)

    MakeSystemModule(sysBkt,mod);
    mod^.loaded := TRUE;
    pScope := NIL;
    InsertCastProc();
    InsertType('WORD',wordSize,words,m2_word);
    InsertType('BYTE',byteSize,bytes,m2_byte);
    InsertType('ADDRESS',adrSize,adrs,m2_adr);
   (* ensure that ADDRESS == POINTER TO BYTE *)
    stdTp[adrs]^.targetType := stdTp[bytes];
    InsertAlias('LOC',stdTp[bytes]);
    InsertStdProc('TSIZE',tsizeP,stFunc);
    InsertStdProc('ADR',adrP,stFunc);
    InsertStdProc('INCADR',addAdrP,stFunc);
    InsertStdProc('ADDADR',addAdrP,stFunc);
    InsertStdProc('DECADR',subAdrP,stFunc);
    InsertStdProc('SUBADR',subAdrP,stFunc);
    InsertStdProc('DIFADR',difAdrP,stFunc);
    InsertStdProc('SHIFT',shiftP,stFunc);
    InsertStdProc('ROTATE',rotateP,stFunc);
    InsertStdProc('ENTIER',entierP,stFunc);
    InsertStdProc('ROUND',roundP,stFunc);
    mod^.exports := pScope;

    InsertBitset; (* must come after system scope defined *)

    (* now for ProgArgs *)
    EnterString("ProgArgs",hsh);
    MakeSystemModule(hsh,mod);
    pScope := NIL;
    InsertStdProc('UNIXexit',exitP,stProc);
    InsertStdProc('UNIXtime',timeP,stFunc);
    InsertAssertProc();
    mod^.exports := pScope;

    (* now for HugeInts *)
    EnterString("HugeInts",hsh);
    MakeSystemModule(hsh,mod);
    pScope := NIL;
    InsertType('HUGEINT',doubleSize,hInts,anonBkt);
    InsertStdProc('HTRUNC', htruncP, stFunc);
    InsertStdProc('HROUND', hroundP, stFunc);
    InsertStdProc('HENTIER',hentierP,stFunc);
    InsertStdProc('HUGE',   hugeP,   stFunc);
    mod^.exports := pScope;

    (* now for StringsOfAnytype *)
    EnterString("VARSTRS",hsh);
    MakeSystemModule(hsh,mod);
    pScope := NIL;
    InsertStdProc('APPEND',appendP,stProc);
    InsertStdProc('CONCAT',concatP,stProc);
    InsertStdProc('CUT',resetP,stProc);
    mod^.exports := pScope;
    strMod := mod;
  END Initialize;

  PROCEDURE ExclStrExt;
  BEGIN strMod^.exports := NIL END ExclStrExt;

  PROCEDURE PointerTo(obj : TyNodeClass) : TypeDesc;
  BEGIN RETURN stdTp[obj] END PointerTo;

  PROCEDURE CastIdDesc() : IdDesc;
  BEGIN RETURN cstPtr END CastIdDesc;

  PROCEDURE AssertIdDesc() : IdDesc;
  BEGIN RETURN assrtP END AssertIdDesc;

  PROCEDURE PreconIdDesc() : IdDesc;
  BEGIN RETURN precnP END PreconIdDesc;

  VAR ix : TyNodeClass;

BEGIN
  FOR ix := chars TO SS DO stdTp[ix] := NIL END;
END M2TabInitialize.
