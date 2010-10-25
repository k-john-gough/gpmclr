(****************************************************************)
(*                                                              *)
(*              Modula-2 Compiler Source Module                 *)
(*                                                              *)
(*          Tree Traversal and ObjectCode Production            *)
(*            MODIFIED VERSION FOR CLR IL OUTPUT                *)
(*                                                              *)
(*      (c) copyright 1988 Faculty of Information Technology    *)
(*      (c) copyright 2003 Faculty of Information Technology    *)
(*                                                              *)
(*      original module : kjg May 1988                          *)
(*      modifications   : CLR version kjg June 2003             *)
(*                                                              *)
(****************************************************************)

IMPLEMENTATION MODULE M2ClrCode;

  IMPORT StdError, M2IL;

  FROM Types    IMPORT Card16;
  FROM SYSTEM   IMPORT CAST;
  FROM Storage  IMPORT ALLOCATE, DEALLOCATE;
  FROM VARSTRS  IMPORT APPEND;
  FROM ProgArgs IMPORT Assert;
  FROM HugeInts IMPORT HUGE;

  FROM GenSequenceSupport IMPORT
        Sequence, IsEmpty, Ended, ElemPtr, InitCursor, LinkRight, LinkLeft,
        InitSequence, LinkRight, DisposeList, GetFirst, GetNext,
        LengthOf, NextIsLast;

  FROM M2NodeDefs IMPORT
        VarUses,
        CreateIdDesc, (* Sep-92 *)
        CreateTypeDesc, (* Oct-93 *)
        IdTree, TreeRec, FormalClass,
        IdString, IdDesc, IdRec, IdNodeClass, IdClassSet,
        StandardProcs,
        TyString, TypeDesc, TypeRec, TyNodeClass, TyClassSet,
        StrucTree, StrucRec, globalModList,
        FormalType, FormalRec,
        Attribute, AttributeSet, modState,
        thisCompileUnit;

  FROM M2InOut IMPORT
        CreateObjFile, CloseObjFile, 
        DiagName, Position, debugOn;

  FROM M2StructureDefs IMPORT
        CaseString, PartString,
        StatDesc, StatRec, StatNodeClass,
        RangeDesc, RangeRec, IfDesc, IfRec,
        CaseDesc, CaseRec, CaseStatRec;

  FROM M2Designators   IMPORT
        ExprDesc, ExprRec, AccessModeOf, ExprNodeClass,
        InitDesignator, ForceAccessMode, (* Sep-92 *)
        SelectNodeClass, InitDState, EmptySelList, DesigRec,
        GetSelector, DStateType, SelectAttribute,
        AccessMode, ActualParMode;

  FROM M2RefFile IMPORT WriteRefFile;

  FROM M2CilWrappers IMPORT WriteWrappers;

  FROM M2SSUtilities   IMPORT
        OrdinalValue, MinOfOrdType, MaxOfOrdType, IsOrdinalType, 
        IsSignedType, Compatible, IndexCardinality;

  FROM M2Alphabets     IMPORT 
        ModStateFlags, Spellix, HashBucketType, LexAttType, 
        Flags, FlagSet, ConBlock;

  FROM M2CILwriter IMPORT
        CatEnum, GetVectorBlob, GetVectorHigh, PutVectorHigh, 
        GetVectorLimit, CallVectorConcat, CallVectorExpand,
        CallVectorCtor, CallVectorDtor, GetBlobAddress,
        TempIndex, invalid, 
        JumpTabDesc, Switch, CreateJumpTable,
        ClassBegin, ClassEnd, EmitMyVars, PushModName,
        newBlobTypeTemp, newTemp, newPinTemp, FreeTemp, 
        TempList, NewGroup, FreeGroup,
        MakeTemp, StoreTemp, PushTemp, PushTempAdr, 
        Duplicate, Pop,
        PushAndPostIncTemp, PreDecAndPushTemp,
        LabString, WriteComment, CommentStart, CommentEnd,
        NamespaceBegin, NamespaceEnd, 
        EmitClassDefs, DoPInvokeImpls,
        DoObjHeader, EmitLitChain, DoObjEnd,
        AllocLabel, CodeLabel, CommentLabel, LineNum, 
        PushCon, PushAdr, PushVal, 
        PushCrd, PushInt, PushChr, PushHuge, PushHugeMax, PushHugeMin,
        CopyBlock, StoreVal, StoreInd, LoadInd, 
        LoadObj, StoreObj, PushZero,
        CallTos, CallMth, MkTrap, RtsHelper, TrapEnum, RtsCallEnum,
        Add, Sub, Mul, Slash,
        DivU, DivI, DivH, ModU, ModI, ModH, RemI, RemH, RemU, 
        AddOffset, Neg, NegBits, NegBool, 
        LShift, RShift, Shift, LRShift,
        BitOR, BitAND, BitXOR,
        Branch, BranchEQZ, BranchNEZ,
        IntRelop, CardRelop, FltRelop, 
        BigSetRelop, SetRelop, SetInOp, 
        IntRelopTrue, CardRelopTrue, FltRelopTrue, 
        IntRelopFalse, CardRelopFalse, FltRelopFalse,
        DFloat, FFloat, 
        TruncU, TruncI, HTrunc, HEntier, HRound,
        FloorD, FloorF, RoundD, RoundF,
        MkR64, MkR32, MkCrd,
        MkI32, ConvItoI64, ConvUtoI64, 
        MkU32, MkU8, AbsVal,
        hasXSR, DefineXSR, callSmbl,
        EmitWrapper, GenerateEntry, GenerateExit, PushStaticLink, Return;

  FROM M2TabInitialize IMPORT PointerTo;

  FROM M2IL IMPORT Object, LabelType, ModeEnum;

  FROM M2MachineConstants IMPORT 
        bigEndian, bitsInWord, bytesInWord, parsFixed,
        alignMap, bytesInReal;

  FROM M2NameHandler   IMPORT EnterString, StringTable, GetSourceRep;
  FROM M2LitChain      IMPORT literalZero;

  CONST invariant = unresolved;
        localT    = directLocl;
        pointerT  = indirect;
        unknownT  = refOverwrite;

  VAR   hMinBkt, hMaxBkt, xpndBkt : HashBucketType;


 (* ============================================================ *)
 (*  This nested module replaces the functionality of module     *)
 (*  M2ProcState, for the CLR version.                           *)
 (*  Author: kjg 2003.                                           *)
 (* ============================================================ *)
  MODULE ClrProcState;

    IMPORT 
        TypeDesc, TyNodeClass, ExprDesc, FormalClass, IdNodeClass, 
        FormalType, bytesInWord, Assert, PointerTo, ALLOCATE,
        Sequence, ElemPtr, InitSequence, InitCursor, Ended, GetNext, 
        LinkRight;
        
    EXPORT 
        ClrMode, ParInfo, GetActuals;

    TYPE 
        ClrMode = (pushVal, pushRef, refToArr, copyObj, localCopy);

      ParInfo = POINTER TO RECORD
                  frmTyp : TypeDesc;
                  actExp : ExprDesc;
                  clrMod : ClrMode;
                END;

VAR glob : ParInfo;

   (* --------------------------------------------------------- *)
   (* There are several patterns in passing actual params to    *)
   (* the CLR ---                                               *)
   (*  (1)  Just push the scalar value on the evaluation stack. *)
   (*       This is the case for scalar, value-mode formals.    *)
   (*  (2)  Just push a reference to the value onto the stack.  *)
   (*       This is always the case for var-mode params, for    *)
   (*       formals of scalar and value types.                  *)
   (*  (2b) Formals of var-mode open arrays also have their     *)
   (*       addresses pushed but get a distinguished tag value. *)
   (*  (3)  Push a reference to the value, then emit opc_cpobj. *)
   (*       This is the case for formals of types that have     *)
   (*       value class representation: fixed arrays, records.  *)
   (*  (4)  Make a copy in the caller, then push a reference.   *)
   (*       This is the case for value-mode open arrays.        *)
   (* --------------------------------------------------------- *)

   (* --------------------------------------------------------- *)
   (*     (pushVal, pushRef, refToArr, copyObj, localCopy);     *)
   (* --------------------------------------------------------- *)
    PROCEDURE getMode(frm : FormalType) : ClrMode;
      VAR rslt : ClrMode;
    BEGIN
      CASE frm^.form OF
      | openHiForm   : rslt := pushVal;
      | varForm      : rslt := pushRef;
      | openValForm  : rslt := localCopy;
      | openVarForm  : rslt := refToArr;
      | valForm      : 
          CASE frm^.type^.tyClass OF
          | arrays, records, unions :
                       rslt := copyObj;
          | stringTs : rslt := pushVal; (* i.e. ref. semantics *)
          | sets     : IF frm^.type^.size> bytesInWord THEN 
                         rslt := copyObj;
                       ELSE 
                         rslt := pushVal;
                       END;
          ELSE
                       rslt := pushVal;
          END;
      END;
      RETURN rslt;
    END getMode;
   (* -------------------------------------------------------- *)

    PROCEDURE GetActuals(aSeq : Sequence;   (* Sequence of ExprDesc *)
                         pTyp : TypeDesc;   (* Procedure TypeDesc   *)
                     VAR oSeq : Sequence);  (* Sequence of ParInfo  *)
      VAR aCurs : ElemPtr;     (* actual param. cursor *)
          fCurs : ElemPtr;     (* formal param. cursor *)
          aElem : ExprDesc;    (* selected actual elem *)
          fElem : FormalType;  (* selected formal elem *)
          oElem : ParInfo;     (* output sequence elem *)
          pInvk : BOOLEAN;     (* interface => no high *)
          hIndx : CARDINAL;
    BEGIN
oElem := glob;

      pInvk := (pTyp^.parentMod^.idClass = exportNode) AND
                                             pTyp^.parentMod^.direct;
      InitSequence(oSeq);
      InitCursor(aSeq, aCurs);
      InitCursor(pTyp^.params, fCurs);
      WHILE NOT Ended(aCurs) DO
        GetNext(aCurs, aElem);
        GetNext(fCurs, fElem);
        NEW(oElem);
        oElem^.actExp := aElem;
        oElem^.frmTyp := fElem^.type;
        oElem^.clrMod := getMode(fElem);
        LinkRight(oSeq, oElem);
       (*
        *  Now deal with any additional "high" values.
        *)
        IF (fElem^.form >= openValForm) AND NOT pInvk THEN
          FOR hIndx := 1 TO fElem^.dimN DO
            GetNext(aCurs, aElem);
            NEW(oElem);
            oElem^.actExp := aElem;
            oElem^.frmTyp := PointerTo(cards);
            oElem^.clrMod := pushVal;
            LinkRight(oSeq, oElem);
          END;
        END;
      END;
    END GetActuals;

  END ClrProcState;
(* ============================================================ *)
(* ============================================================ *)

  CONST BranchFalse = BranchEQZ;
        BranchTrue  = BranchNEZ;

(* ============================================================ *)

  TYPE  ClassMap = ARRAY TyNodeClass OF Object;

  CONST specials = TyClassSet{arrays,records,SS};
     (* this is the set of classes which require special assignment *)
     (* in the following table specials have the dummy entry word  *)

  CONST realClasses   = TyClassSet{RR, floats, doubles};
        scalarClasses = TyClassSet{II .. bytes, procTypes .. S1, subranges};

  CONST procSet = IdClassSet{procNode, procHeader, externProc, cilWrapper};

  CONST table = ClassMap{word,word,word,double, (* II, ZZ, UU, RR, *)
        		 byteCard, word, byteCard, byteCard, word, word,
        		 hugeInt,
        		 float,	 (* short-real *)
        		 double, (* long-real  *)
        		 word, word, byteCard, word,
        		 word, word, word, word,
        		 word, (* imported opaque *)
        		 word, (* own opaque type *)
        	         word, (* stringTs *)
        		 word, byteCard, word, word, word};

  VAR   inExcept     : BOOLEAN;
        exceptDesc   : IdDesc;	     (* exception descriptor *)
        retryLab     : LabelType;    (* emitted in normal body if hasExcept *)
        returnLab    : LabelType;

  VAR	charPtr      : TypeDesc;


  TYPE  ModeMap = ARRAY (* sign *)BOOLEAN, (* test *)BOOLEAN OF ModeEnum;
  CONST divMode = ModeMap{{crdV,crdV},{intV,intV}};
        addMode = ModeMap{{none,crdV},{none,intV}};

  (* ================================================== *)

  PROCEDURE baseObjOf(ty : TypeDesc) : Object;
  BEGIN
    IF ty^.tyClass <> subranges THEN RETURN table[ty^.tyClass] END;
    CASE ty^.size OF
    | 1 : IF IsSignedType(ty) THEN RETURN byteInt;
          ELSE RETURN byteCard;
          END;
    | 2 : IF IsSignedType(ty) THEN RETURN shortInt;
          ELSE RETURN shortCard;
          END;
    | 4 : IF    bytesInWord = 4  THEN RETURN word;
          ELSIF IsSignedType(ty) THEN RETURN longInt;
          ELSE RETURN longCard;
          END;
    | 8 : RETURN word;
    END;
  END baseObjOf;

  PROCEDURE baseTypeOf(ty : TypeDesc) : TypeDesc;
  BEGIN
    IF ty^.tyClass = subranges THEN RETURN ty^.hostType;
    ELSE RETURN ty;
    END;
  END baseTypeOf;

  (* ================================================== *)

  PROCEDURE needsCopy(class : TyNodeClass; size : CARDINAL) : BOOLEAN;
  BEGIN
    RETURN (class IN specials) OR ((class = sets) AND (size > bytesInWord));
  END needsCopy;

  (* ================================================== *)

  PROCEDURE typeOfDes(des : DesigRec) : TypeDesc;
    VAR typ : TypeDesc;
        stt : DStateType;
        val : SelectAttribute;
  BEGIN
    IF des.variable^.idClass = varNode  THEN
      typ := des.variable^.varType;
    ELSIF des.variable^.idClass IN procSet THEN
      typ := des.variable^.procType;
    END;
    IF  NOT EmptySelList(des) THEN
      InitDState(des,stt);
      LOOP
        IF typ^.tyClass = opaqueTemp THEN
          typ := typ^.resolvedType
        END;
        GetSelector(stt,val);
        CASE val.tag OF
        | endMarker        : EXIT;
        | dereferenceNode  : typ := typ^.targetType;
        | fieldExtractNode : typ := val.fid^.fieldType;
        | subscriptNode    : 
            IF typ^.tyClass = stringTs THEN
              typ := typ^.targetType;
            ELSE
              typ := typ^.elementType;
            END;
        END;
      END;
    END;
    RETURN typ;
  END typeOfDes;

  (* ================================================== *)
  MODULE InLineTests;
    IMPORT ModeEnum,
           GetVectorHigh, PushVal,
           MkTrap, TrapEnum, WriteComment,
           AllocLabel, AccessMode,
           bytesInWord, HUGE, PushHuge,
           PushCrd, PushInt, LoadInd,
           MinOfOrdType, MaxOfOrdType, IsSignedType,
           IsOrdinalType, ExprNodeClass, Object,
           IntRelopTrue, CardRelopTrue, 
           IntRelopFalse, CardRelopFalse, 
           PushAdr, PushTemp, PushHugeMin,
           TempIndex, AddOffset,
           MakeTemp, Duplicate,
           Add, Sub, IdDesc, 
           TyNodeClass, TypeDesc, CodeLabel, LabelType;

    EXPORT IndexCheck, OpenIndexCheck, VectorIndexCheck, 
           Test, ModTest, MinIntTest, VariableCheck, NonNegCheck;

    VAR xLab : LabelType;

    PROCEDURE ModTest(cls : TyNodeClass);
      VAR exitLab : LabelType;
    BEGIN
      AllocLabel(xLab);
      Duplicate();
      IF cls = hInts THEN 
(*
 *    For some reason, gpm does a 2-quadrant MOD and DIV for INTEGERS,
 *    but performs a 4-quadrant version for 64-bit integers.
 *
 *      PushHuge(HUGE(1));
 *      IntRelopFalse(lessNode, xLab);
 *)
        PushHuge(HUGE(0));
        IntRelopFalse(equalsNode, xLab);
      ELSE 
        PushInt(1);
        IntRelopFalse(lessNode, xLab);
      END;
      MkTrap(modTrp);
      CodeLabel(xLab);
    END ModTest;

    PROCEDURE MinIntTest(cls : TyNodeClass);
      VAR exitLab : LabelType;
    BEGIN
      IF cls = ints THEN
        Duplicate();
        PushCrd(80000000H);
      ELSIF cls = hInts THEN
        Duplicate();
        PushHugeMin;
      ELSE RETURN;
      END;
      AllocLabel(xLab);
      CardRelopFalse(equalsNode, xLab);
      MkTrap(minIntTrp);
      CodeLabel(xLab);
    END MinIntTest;

    PROCEDURE DblTst(low, high : CARDINAL);
    (* pre    : value to be tested is on top of stack   *)
    (* post   : value still on top, test is emitted     *)
    BEGIN
      WriteComment("double ended range check");
      Duplicate;
      IF low <> 0 THEN
        PushCrd(low);
        Sub(none);
      END;
(* $T- *)
      PushCrd(high - low);
(* $T= *)
      CardRelopFalse(greaterNode, xLab);
      (* now value is on tos again *)
      Duplicate;                  (* dubious? *)
      PushCrd(high);
      PushCrd(low);
    END DblTst;

    PROCEDURE UppTst(high : CARDINAL);
    (* pre    : value to be tested is on top of stack   *)
    (* post   : value still on top, test is emitted     *)
    BEGIN
      WriteComment("upper bound range check");
      Duplicate;
      PushCrd(high);
      CardRelopFalse(greaterNode, xLab);
      (* now value is on tos again *)
      Duplicate;                  (* dubious? *)
      PushCrd(high);
    END UppTst;

    PROCEDURE LowTst(low : INTEGER);
    (* pre    : value to be tested is on top of stack   *)
    (* post   : value still on top, test is emitted     *)
    BEGIN
      WriteComment("lower bound range check");
      Duplicate;
      PushInt(low);
      IntRelopFalse(lessNode, xLab);
      (* now value is on tos again *)
      Duplicate;                  (* dubious? *)
      PushInt(low);
    END LowTst;

    PROCEDURE OpenIndexCheck(hiDes : IdDesc;
        		     uplev : BOOLEAN);
    BEGIN
      WriteComment("array index check");
      AllocLabel(xLab);
      Duplicate;
      IF uplev THEN 
        PushAdr(hiDes, uplevel);
        LoadInd(word);		(* high value is tos *)
      ELSE 
        PushVal(hiDes, directLocl, word);
      END;
      CardRelopTrue(lessEqNode,xLab);
      Duplicate;                  (* dubious? *)
      IF uplev THEN 
        PushAdr(hiDes,uplevel);
        LoadInd(word);		(* high value is tos again *)
      ELSE 
        PushVal(hiDes, directLocl, word);
      END;
      PushCrd(0);
      MkTrap(indexLHU);
      CodeLabel(xLab);
    END OpenIndexCheck;

    PROCEDURE NonNegCheck();
    BEGIN
      WriteComment("non negative check");
      AllocLabel(xLab);
      Duplicate;
      PushCrd(0);
      IntRelopFalse(lessNode, xLab);
      PushCrd(0);
      MkTrap(rangeLI);
      CodeLabel(xLab);
    END NonNegCheck;

    PROCEDURE VectorIndexCheck(dsTmp : TempIndex);	(* descriptor tmp *)
    BEGIN
     (* pre: stack has blob-pointer value, then index value at top *)
      WriteComment("vector index check");
      Duplicate;
      AllocLabel(xLab);
      PushTemp(dsTmp);
      GetVectorHigh();
      CardRelopTrue(lessEqNode, xLab);
      Duplicate;
      PushTemp(dsTmp);
      GetVectorHigh();
      PushCrd(0);
      MkTrap(indexLHI);
      CodeLabel(xLab);
    END VectorIndexCheck;

    PROCEDURE VariableCheck(tmp : TempIndex; low : INTEGER);
      (* checks that tos is in [low .. tmpVal] *)
    BEGIN
      WriteComment("inline range check");
      AllocLabel(xLab);
      Duplicate;
      IF low <> 0 THEN		(* fix kjg Sep-92 *)
        PushInt(low);		
        Sub(none);
        PushTemp(tmp);
        PushInt(low);
        Sub(none);  (* max is on tos, test val below *)
      ELSE
        PushTemp(tmp);
      END;
      CardRelopFalse(greaterNode, xLab);
      (* error, trap must be emitted *)
      Duplicate;                  (* dubious? *)
      PushTemp(tmp);
      PushInt(low);
      MkTrap(rangeLHI);
      CodeLabel(xLab);
    END VariableCheck;

    PROCEDURE IndexCheck(typ : TypeDesc);
      VAR min,max : INTEGER;
    BEGIN
      AllocLabel(xLab);
      DblTst(typ^.minRange,typ^.maxRange);
      IF IsSignedType(typ) THEN
        MkTrap(indexLHI);
      ELSE
        MkTrap(indexLHU);
      END;
      CodeLabel(xLab);
    END IndexCheck;

    PROCEDURE Test(dstTyp : TypeDesc;
                   srcTyp : TypeDesc);
    (* assert : value is on top of stack *)

        TYPE TrickWord = RECORD
                           CASE : BOOLEAN OF
                           | TRUE  : c : CARDINAL;
                           | FALSE : i : INTEGER;
                           END;
                         END;

        VAR  dSgnd  : BOOLEAN;
             dMin, dMax, sMin, sMax : TrickWord;
      BEGIN
        IF NOT IsOrdinalType(dstTyp) THEN RETURN END;
        IF srcTyp^.tyClass = hInts THEN RETURN END;
        dSgnd  := IsSignedType(dstTyp);
        dMin.c := MinOfOrdType(dstTyp);
        dMax.c := MaxOfOrdType(dstTyp);
        sMin.c := MinOfOrdType(srcTyp);
        sMax.c := MaxOfOrdType(srcTyp);
        (*
         *  calculate overlap expressed in srcTyp terms
         *)
        AllocLabel(xLab);
        IF IsSignedType(srcTyp) THEN (* signed source *)
          IF NOT dSgnd AND (dMax.i < 0) THEN dMax.i := sMax.i END;
          IF (sMin.i >= dMin.i) AND (sMax.i <= dMax.i) THEN
            (* skip *)
          ELSIF sMax.i <= dMax.i THEN
            (*
             *  signed, single ended check of value
             *  against the min bound of destination
             *)
            LowTst(dMin.i);
            MkTrap(rangeLI);
            CodeLabel(xLab);
          ELSE 
            (*
             *  signed and double ended checks 
             *  are done using the cardinal tests
             *  but jump to the alternate trap point
             *)
            DblTst(dMin.c,dMax.c);
            MkTrap(rangeLHI);
            CodeLabel(xLab);
          END;
        ELSE (* unsigned source *)
          IF dSgnd AND (dMin.i < 0) THEN dMin.c := 0 END;
          IF sMin.c >= dMin.c THEN
            IF sMax.c <= dMax.c THEN (* skip *)
            ELSE (* single ended check *)
              UppTst(dMax.c);
              MkTrap(rangeHU);
              CodeLabel(xLab);
            END;
          ELSE (* double ended check *)
            DblTst(dMin.c,dMax.c);
            MkTrap(rangeLHU);
            CodeLabel(xLab);
          END;
        END;
    END Test;

  END InLineTests;
  (* ================================================== *)
 
  TYPE  ExprClassSet = SET OF ExprNodeClass;
  CONST setBinops = ExprClassSet{starNode,slashNode,plusNode,minusNode};
        binops = ExprClassSet{andNode .. inNode};

  (* ================================================== *)
 
  PROCEDURE ConstDesignator(exp : ExprDesc);
  (* post : the address of the designator is on the top of stack *)
  BEGIN
    PushCon(exp^.rtOffset);
    IF NOT EmptySelList(exp^.name) THEN Designator(exp^.name, TRUE) END;
  END ConstDesignator;

  PROCEDURE DerefDesig(des : DesigRec; obj : Object);
    VAR mod : AccessMode;
  BEGIN
    mod := AccessModeOf(des);
    IF EmptySelList(des) THEN 
      PushVal(des.variable, mod, obj);
    ELSE
      Designator(des, FALSE);
      LoadInd(obj);
    END;
  END DerefDesig;

  PROCEDURE isSimpleDes(des : DesigRec; mod : AccessMode) : BOOLEAN;
  BEGIN
    RETURN EmptySelList(des) AND ((mod = directLocl) OR (mod = directNonL));
  END isSimpleDes;

 (* ================================================== *)

  PROCEDURE PushOpenElemSize(high : IdDesc; 
                            elTyp : TypeDesc; 
                            uplev : BOOLEAN);

    PROCEDURE realElType(first : IdDesc; elTyp : TypeDesc) : TypeDesc;  
    BEGIN
      WHILE first <> NIL DO	(* find real element type ... *)
        elTyp := elTyp^.elementType;
        first := first^.nextHigh;
      END;
      RETURN elTyp;
    END realElType;

  BEGIN
    high  := high^.nextHigh;
    elTyp := realElType(high,elTyp);
    PushCrd(elTyp^.size);
    WHILE high <> NIL DO
      IF uplev THEN
        PushAdr(high, uplevel);
        LoadInd(word);                      (* high value is tos *)
      ELSE
        PushVal(high, highAccess, word);    (* high value is tos *)
      END;
      PushCrd(1);
      Add(none);
      Mul(none);
      high  := high^.nextHigh;
    END;
  END PushOpenElemSize;

 (* ================================================== *)

  PROCEDURE constPart(exp : ExprDesc) : CARDINAL;
  BEGIN
(* $T- *)      (* these incs and decs could be by signed amounts ... *)
    WITH exp^ DO 
      IF exprClass = literalNode THEN
        RETURN OrdinalValue(exprType,conValue);
      ELSIF exprClass = plusNode THEN
        RETURN constPart(leftOp) + constPart(rightOp);
      ELSIF exprClass = minusNode THEN
        RETURN constPart(leftOp) - constPart(rightOp);
      ELSIF (exprClass = starNode) THEN
        IF (rightOp^.exprClass = literalNode) THEN 
          RETURN constPart(leftOp) * 
        		OrdinalValue(rightOp^.exprType,rightOp^.conValue);
        ELSIF (leftOp^.exprClass = literalNode) THEN 
          RETURN constPart(rightOp) * 
        		OrdinalValue(leftOp^.exprType,leftOp^.conValue);
        ELSE RETURN 0;
        END;
      ELSE RETURN 0;
      END;
    END;
(* $T= *)
  END constPart;

  PROCEDURE PushVariablePart(exp : ExprDesc);
    VAR hasLOp,hasROp : BOOLEAN;
  BEGIN
(* $T- *)	(* these incs and decs could be by signed amounts ... *)
    WITH exp^ DO
      Assert(exprClass <> literalNode,"PushVarPart on literal!");
      hasLOp := FALSE; hasROp := FALSE;
      IF exprClass = plusNode THEN
        IF leftOp^.exprClass <> literalNode THEN
        	  PushVariablePart(leftOp); hasLOp := TRUE END;
        IF rightOp^.exprClass <> literalNode THEN
        	  PushVariablePart(rightOp); hasROp := TRUE END;
        IF hasLOp AND hasROp THEN Add(none) END;
      ELSIF exprClass = minusNode THEN
        IF leftOp^.exprClass <> literalNode THEN
        	  PushVariablePart(leftOp); hasLOp := TRUE END;
        IF rightOp^.exprClass <> literalNode THEN
        	  PushVariablePart(rightOp); hasROp := TRUE END;
        IF hasLOp AND hasROp THEN Sub(none);
        ELSIF hasROp THEN Neg();
        END;
      ELSIF (exprClass = starNode) AND
            ((rightOp^.exprClass = literalNode) OR
             (leftOp^.exprClass = literalNode)) THEN
        IF rightOp^.exprClass = literalNode THEN
          PushVariablePart(leftOp);
          PushCrd(OrdinalValue(rightOp^.exprType, rightOp^.conValue));
        ELSE (* leftOp is literal *)
          PushVariablePart(rightOp);
          PushCrd(OrdinalValue(leftOp^.exprType, leftOp^.conValue));
        END;
        Mul(none);
      ELSE PushExprValue(exp);
      END;
    END;
(* $T= *)
  END PushVariablePart;

(* ------------------------------------------------------- *)

  PROCEDURE Designator(desg : DesigRec;   (* Designator to push lvalue of *)
                       pshd : BOOLEAN);   (* Base address already pushed  *)
    VAR dState  : DStateType;
        currTp  : TypeDesc;
        indTp   : TypeDesc;
        highD   : IdDesc;
        attrib  : SelectAttribute;
        elSize  : CARDINAL;
        sizeOpn : BOOLEAN;
        isUplev : BOOLEAN;
        idxTmp  : TempIndex;
        size    : CARDINAL;
        accMode : AccessMode;
        offsetTotal : INTEGER;
        constIndex, lVal : CARDINAL;

    PROCEDURE ScaleAndAddSize(siz   : CARDINAL); 
    BEGIN
      IF siz > 1 THEN PushCrd(siz); Mul(none) END;
      Add(none);
    END ScaleAndAddSize;

    PROCEDURE ScaleAndAddOpen(curTp : TypeDesc;
                              highD : IdDesc;
                              uplev : BOOLEAN);
    BEGIN
      PushOpenElemSize(highD, curTp, uplev);
      Mul(none);
      Add(none);
    END ScaleAndAddOpen;

  BEGIN
    offsetTotal := 0;
    InitDState(desg,dState);
    highD  := desg.variable;
    currTp := desg.variable^.varType;
    accMode := AccessModeOf(desg);
    isUplev := accMode >= uplevel;

(* $T-  all offsets are calculated modulo 2**32 *)

    LOOP
     (*
      *  If the current type is an opaque temp we
      *  must resolve it to the real pointer type.
      *  (How did this one escape until 1996? kjg)
      *)
      IF (currTp # NIL) AND 
         (currTp^.tyClass = opaqueTemp) THEN currTp := currTp^.resolvedType END;

      GetSelector(dState, attrib);
      IF NOT pshd THEN
       (*
        *   For the usual call of Designator() the second arg is FALSE.
        *   This value denotes that the address of the entire variable
        *   has not been pushed.  The native code versions just go ---
        *      pushAdr <desig>
        *      <optional selectors>
        *   This will not do for IL, because for a pointer the pattern --
        *      ldloc.a NN
        *      ldind.i4
        *   prevents the local from being promoted to a register. Thus
        *   we defer pushing the address. If the first selector is deref.
        *   we do "PushVal" instead of "PushAdr; LoadInd".
        *)
        IF attrib.tag = dereferenceNode THEN
          PushVal(desg.variable, accMode, word);
          currTp := currTp^.targetType;
          IF currTp^.tyClass=opaqueTemp THEN currTp:=currTp^.resolvedType END;
          GetSelector(dState, attrib);
        ELSE
          PushAdr(desg.variable, accMode);
        END;
        pshd := TRUE;
      END;

      CASE attrib.tag OF
        | fieldExtractNode :
            INC(offsetTotal, attrib.fid^.fieldOffset);
            currTp := attrib.fid^.fieldType;
        | subscriptNode :
            IF currTp^.tyClass = stringTs THEN
              IF offsetTotal <> 0 THEN		(* -|,ptr	*)
                AddOffset(offsetTotal);
                offsetTotal := 0;
              END;
              LoadInd(word);
              IF indexTests IN attrib.exp^.testFlags THEN
                idxTmp := newTemp(PointerTo(adrs));
                MakeTemp(idxTmp);
              END;
              GetVectorBlob(); (* fetch the blob pointer field *)
             (*
              *  Deal with new (Jul 1996) string types.
              *  Layout of stringtype is ...
              *
              *    ptr	       blk	     mem
              *   [===] ---> +-----+
              *              |    -+-----> +-----+
              *              | hi  |       |     | num * size
              *              | num |       |     |
              *              +-----+       v     v
              *)
              currTp  := currTp^.targetType;
              PushExprValue(attrib.exp);
              IF indexTests IN attrib.exp^.testFlags THEN
                VectorIndexCheck(idxTmp);
                FreeTemp(idxTmp);
              END;
              size := currTp^.size;
              IF size # 0 THEN 
                ScaleAndAddSize(size);
              ELSE 
                ScaleAndAddOpen(currTp, highD, isUplev);
              END;
            ELSIF (currTp^.tyClass = arrays) AND currTp^.isDynamic THEN
             (*
              *  Deal with indexing into open arrays.
              *)
              currTp  := currTp^.elementType;
              sizeOpn := (currTp^.tyClass = arrays) AND currTp^.isDynamic;
              highD   := highD^.nextHigh;
              IF sizeOpn THEN
                elSize := 0;
              ELSE
                elSize := currTp^.size;
              END;
              WITH attrib.exp^ DO
                IF (exprClass = literalNode) AND
                     NOT (indexTests IN testFlags) THEN
(* $T- *)         (* these incs and decs could be by signed amounts ... *)
                  INC(offsetTotal,OrdinalValue(exprType,conValue) * elSize);
(* $T= *)       ELSE (* not a literal, or needs index check *)
                  PushExprValue(attrib.exp);
                  IF indexTests IN testFlags THEN
                    IF exprType^.hiDesc <> highD THEN
                      OpenIndexCheck(highD, isUplev);
                    ELSIF exprType^.minRange > MAX(INTEGER) THEN
                      MkU32(TRUE);
                    END;
                  END;
                  size := currTp^.size;
                  IF size # 0 THEN 
                    ScaleAndAddSize(size);
                  ELSE 
                    ScaleAndAddOpen(currTp, highD, isUplev);
                  END;
                END;
              END; (* with *)
            ELSE 
             (*
              *  Deal with indexing into ordinary arrays.
              *)
              indTp   := currTp^.indexType;     (* the target index type *)
              currTp  := currTp^.elementType;
              lVal    := MinOfOrdType(indTp);
              elSize := currTp^.size;
(* $T- *)     DEC(offsetTotal,lVal * elSize);
(* $T= *)     WITH attrib.exp^ DO
                IF (exprClass = literalNode) AND
                        NOT (indexTests IN testFlags) THEN
(* $T- *)         (* these incs and decs could be by signed amounts ... *)
                  INC(offsetTotal,OrdinalValue(exprType,conValue) * elSize);
(* $T= *)       ELSE (* not a literal, or needs index check *)
                  IF (indexTests IN testFlags) OR
                             (exprType = PointerTo(bools)) THEN
                    PushExprValue(attrib.exp);
                    IF indexTests IN testFlags THEN
                      IndexCheck(indTp); (* dst type *)
                    END;
                  ELSE
                    PushVariablePart(attrib.exp);
(* $T- *)         (* these incs and decs could be by signed amounts ... *)
                    INC(offsetTotal, constPart(attrib.exp) * elSize);
(* $T= *)         END;
                  size := currTp^.size;
                  IF size # 0 THEN 
                    ScaleAndAddSize(size);
                  ELSE 
                    ScaleAndAddOpen(currTp, highD, isUplev);
                  END;
                END;
              END; (* with *)
            END;
        | dereferenceNode :
            IF offsetTotal <> 0 THEN
              AddOffset(offsetTotal);
              offsetTotal := 0;
            END;
            LoadInd(word);
            currTp := currTp^.targetType;
        | endMarker : 
            IF offsetTotal <> 0 THEN
              AddOffset(offsetTotal);
            END;
            EXIT;
      END; (* case *)
    END;
  END Designator;

(* ------------------------------------------------------- *)

  PROCEDURE PushOpenCount(desig : ExprDesc);
    VAR mod : AccessMode;
        hiD : IdDesc;
  BEGIN
    WITH desig^ DO
      IF (AccessModeOf(name) >= uplevel) 
                             THEN mod := uplevel ELSE mod := highAccess END;
      hiD := name.variable^.nextHigh;
      PushVal(hiD, mod, longCard);
      PushCrd(1);
      Add(none);
      hiD := hiD^.nextHigh;
      WHILE hiD <> NIL DO
        PushVal(hiD, mod, longCard);
        PushCrd(1);
        Add(none);
        Mul(none);
        hiD := hiD^.nextHigh;
      END;
    END;
  END PushOpenCount;

  PROCEDURE PushExprAddress(exp : ExprDesc);
    VAR uTmp : TempIndex;
  BEGIN
    WITH exp^ DO
      CASE exprClass OF
      | desigNode    : Designator(name, FALSE);
      | selConstNode : ConstDesignator(exp);
      | literalNode  : PushCon(rtOffset);
      | castNode     : 
         (*
          *  structure:
          *	source  : ExprDesc  -- points to source expression
          *	needTmp : BOOLEAN   -- does this case need a temp
          *	wrd2wrd : BOOLEAN   -- a possibly shortening cast
          *	tempId  : IdDesc    -- name of temporary variable
          *     exprType : TypeDesc -- destination type descriptor
          *)
          IF needTmp THEN
            PushAdr(tempId, directLocl);
            Duplicate;
            IF needsCopy(source^.exprType^.tyClass,source^.exprType^.size) THEN
              IF source^.exprType^.tyClass = SS THEN
                PushCon(source^.rtOffset);
                IF source^.conValue.strHigh >= exprType^.size THEN
                  PushCrd(exprType^.size);		(* dest size   *)
                ELSE
                  PushCrd(source^.conValue.strHigh + 1); 
                END; 
              ELSE
                uTmp := newTemp(source^.exprType);
                MkObjAndPushAdr(source, uTmp);
                PushCrd(exprType^.size);		(* dest size   *)
                FreeTemp(uTmp);
              END;
              CopyBlock(source^.exprType^.alignMask);
            ELSE
              PushExprValue(source);
              StoreInd(baseObjOf(source^.exprType));
            END;
          ELSE
            PushExprAddress(source);
          END;
      | preconNode :
          StatementSeq(exp^.evalLst,0);
          PushExprAddress(exp^.theCall);
      | funcDesigNode : 
          uTmp := newTemp(exp^.exprType);
          MkObjAndPushAdr(exp, uTmp);
          FreeTemp(uTmp);
      | setDesigNode : 
          Assert(FALSE, "setDesigNode in PushExprAddress");
      | constructorNode : 

          uTmp := newTemp(exp^.exprType);
          MkObjAndPushAdr(exp, uTmp);
          FreeTemp(uTmp);
      ELSE  
        uTmp := newTemp(exp^.exprType);
        MkObjAndPushAdr(exp, uTmp);
        FreeTemp(uTmp);
      END;
    END;
  END PushExprAddress;

 (* ---------------------------------------------------- *)

  PROCEDURE MkObjAndPushAdr(elem : ExprDesc; tix : TempIndex);
   (* post : object is built, and address is pushed   *)
   (*        Value is allocated in tix, almost always *)
  BEGIN
    IF (elem^.exprType^.tyClass = sets) AND
        (elem^.exprType^.size > bytesInWord) THEN
      MkSetAndPushAdr(elem, elem^.exprType^.size DIV bytesInWord, tix);
    ELSIF elem^.exprClass = funcDesigNode THEN
      Assert(tix # invalid);
      PushTempAdr(tix);
      PushFunctionValue(elem, elem^.paramSeq);
      StoreObj(elem^.exprType);
      PushTempAdr(tix);
    ELSIF elem^.exprClass = constructorNode THEN
      Assert(tix # invalid);
      PushTempAdr(tix);
      ConstructSeq(elem);		
    ELSE 
      PushExprAddress(elem);  (* CHECK THIS *)
    END;
  END MkObjAndPushAdr;

 (* ---------------------------------------------------- *)

  PROCEDURE ConstructSeq(elem : ExprDesc);
  (* pre  : dest address in on the top of stack *)
  (* post : top of stack is unchanged by call   *)
    VAR tClass : TyNodeClass;
        eClass : ExprNodeClass;
        exTyp  : TypeDesc;
        eCurs  : ElemPtr;
        range  : RangeDesc; (* lower is value expr, upper is repeat count *)
        object : Object;
        needCp : BOOLEAN;
        count  : CARDINAL;
        repOff : INTEGER;
        uTmp   : TempIndex;  (* overall dest address *)
        eTmp   : TempIndex;  (* element dest address *)
  BEGIN
    InitCursor(elem^.rangeSeq,eCurs);
    uTmp := newTemp(PointerTo(adrs));
    MakeTemp(uTmp);
    WHILE NOT Ended(eCurs) DO
      GetNext(eCurs,range);
      WITH range^ DO
        exTyp  := lower^.exprType;
        tClass := exTyp^.tyClass;
        eClass := lower^.exprClass;
        needCp := needsCopy(tClass, exTyp^.size);
       (* push element destination address *)
        PushTemp(uTmp); 
        AddOffset(elemOffset);
        IF NOT needCp THEN
          PushExprValue(lower);
          IF rangeTests IN lower^.testFlags THEN 
            Test(desigType,exTyp); (* dst,src *)
          END;
          object := baseObjOf(desigType);
          StoreInd(object);	                (* pops the dst adrs *)
        ELSIF eClass = funcDesigNode THEN	(* create res in dst *)
          PushFunctionValue(lower, lower^.paramSeq);
          StoreObj(lower^.exprType);
        ELSIF eClass = constructorNode THEN	(* construct in dest *)
          ConstructSeq(lower); Pop;        	(* pops the dst adrs *)
        ELSE					(* build, then copy  *)
          eTmp := newTemp(lower^.exprType);
          MkObjAndPushAdr(lower, eTmp);
          PushCrd(desigType^.size);
          CopyBlock(exTyp^.alignMask);		(* pops the dst adrs *)
          FreeTemp(eTmp);
        END;
        IF upper <> NIL THEN
          repOff := elemOffset;
          FOR count := 1 TO upper^.count - 1 DO
            INC(repOff, desigType^.size);
            IF needCp THEN
              PushTemp(uTmp); 
              AddOffset(repOff);      	              (* dst *)
              PushTemp(uTmp); 
              AddOffset(elemOffset);	              (* src *)
              PushCrd(desigType^.size);
              CopyBlock(exTyp^.alignMask);
            ELSE 
              PushTemp(uTmp); 
              AddOffset(repOff);	     	      (* dst *)
              PushTemp(uTmp); 
              AddOffset(elemOffset);		      (* src *)
              LoadInd(object);
              StoreInd(object);
            END; (* if *)
          END; (* for *)
        END; (* if upper<>NIL *)
      END; (* with *)
    END; (* while *)
  END ConstructSeq;

 (* ---------------------------------------------------- *)

  PROCEDURE BinCompare(expr : ExprDesc; lab : LabelType; fTrue : BOOLEAN);
    VAR lCls, op   : ExprNodeClass;
        lTyp, rTyp : TypeDesc;
        cCls       : TyNodeClass;  (* Comparison class *)
  BEGIN
    lTyp := expr^.leftOp^.exprType;  
    rTyp := expr^.rightOp^.exprType; 
    IF lTyp^.tyClass = sets THEN
      PushExprValue(expr);
      IF fTrue THEN BranchFalse(lab) ELSE BranchTrue(lab) END;
    ELSE
      cCls := lTyp^.tyClass;
      IF cCls = RR THEN cCls := rTyp^.tyClass END;
      PushExpAsTyClass(expr^.leftOp, cCls);
      PushExpAsTyClass(expr^.rightOp, cCls);
     (*
      *   Do we need a signed or an unsigned comparison?
      *)
      op := expr^.exprClass;
      lCls := expr^.leftOp^.exprClass;
      IF lTyp^.tyClass IN realClasses THEN
        IF fTrue THEN FltRelopFalse(op,lab) ELSE FltRelopTrue(op,lab) END;
      ELSIF (lCls <> literalNode) AND IsSignedType(lTyp) OR 
                                      IsSignedType(rTyp) THEN
        IF fTrue THEN IntRelopFalse(op,lab) ELSE IntRelopTrue(op,lab) END;
      ELSE
        IF fTrue THEN CardRelopFalse(op,lab) ELSE CardRelopTrue(op,lab) END;
      END;
    END;
  END BinCompare;

 (* ---------------------------------------------------- *)

  PROCEDURE FallTrue(exp : ExprDesc; fLab : LabelType);
    VAR class : TyNodeClass;
        local : LabelType;
        size  : CARDINAL;
  BEGIN
    CASE exp^.exprClass OF
    | preconNode :
Assert(FALSE,"precon nodes not implemented here");
       (*
        *      StatementSeq(exp^.evalLst,0);
        *      BoolJump(exp^.theCall,fLab,tLab);
        *)
    | orNode :
        AllocLabel(local);
        FallFalse(exp^.leftOp, local);
        FallTrue(exp^.rightOp, fLab);
        CodeLabel(local);        
    | andNode :
        FallTrue(exp^.leftOp, fLab);
        FallTrue(exp^.rightOp, fLab);
    | equalsNode .. lessEqNode :
        BinCompare(exp, fLab, TRUE);
    | notNode     : 
        FallFalse(exp^.notOp, fLab);
    | literalNode : 
        IF exp^.conValue.fixValue = 0 THEN Branch(fLab) END;
    ELSE
      PushExprValue(exp);
      BranchFalse(fLab);
    END; (* case *)
  END FallTrue;

 (* ---------------------------------------------------- *)

  PROCEDURE FallFalse(exp : ExprDesc; tLab : LabelType);
    VAR class : TyNodeClass;
        local : LabelType;
        size  : CARDINAL;
  BEGIN
    CASE exp^.exprClass OF
    | preconNode :
Assert(FALSE,"precon nodes not implemented here");
      (*
       *      StatementSeq(exp^.evalLst,0);
       *      BoolJump(exp^.theCall,fLab,tLab);
       *)
    | andNode :
        AllocLabel(local);
        FallTrue(exp^.leftOp, local);
        FallFalse(exp^.rightOp, tLab);
        CodeLabel(local);        
    | orNode :
        FallFalse(exp^.leftOp, tLab);
        FallFalse(exp^.rightOp, tLab);
    | equalsNode .. lessEqNode :
        BinCompare(exp, tLab, FALSE);
    | notNode     : 
        FallTrue(exp^.notOp, tLab);
    | literalNode : 
        IF exp^.conValue.fixValue # 0 THEN Branch(tLab) END;
    ELSE
      PushExprValue(exp);
      BranchTrue(tLab);
    END; (* case *)
  END FallFalse;

 (* ---------------------------------------------------- *)

  PROCEDURE WordSetConstructor(expr : ExprDesc);
    VAR baseTy : TypeDesc;
        uTmp   : TempIndex;

    PROCEDURE PushAnElement(range : RangeDesc;
                            bseTy : TypeDesc;
                        VAR tpOrd : TempIndex);
      VAR rtl : BOOLEAN;
    BEGIN
      WITH range^ DO
        rtl := rangeTests IN lower^.testFlags; (* "RangeTestLow" *)
        IF upper = NIL THEN (* single element *)
          PushCrd(1);
          PushExprValue(lower);
          IF rtl THEN Test(bseTy, lower^.exprType) END;
          LShift;
        ELSE (* a range *)
          PushCrd(2);
          PushExprValue(upper);
          IF rtl THEN
            IF tpOrd = invalid THEN tpOrd := newTemp(bseTy) END;
            MakeTemp(tpOrd);
          END;
          IF rangeTests IN upper^.testFlags THEN
            Test(bseTy, upper^.exprType); (* dst,src *)
          END;
          LShift;
          Neg;
          
          PushCrd(1);
          PushExprValue(lower);
          IF rtl THEN VariableCheck(tpOrd, bseTy^.minRange) END;
          LShift;
          Neg;
          BitXOR;
        END; (* else a range *)
      END;
    END PushAnElement;

    VAR rngCrs : ElemPtr;
        thsRng : RangeDesc;
  BEGIN
    uTmp := invalid;
    Assert(NOT IsEmpty(expr^.rangeSeq));
    baseTy := expr^.exprType^.baseType;
    GetFirst(expr^.rangeSeq, rngCrs, thsRng);
    PushAnElement(thsRng, baseTy, uTmp);
    WHILE NOT Ended(rngCrs) DO
      GetNext(rngCrs, thsRng);
      PushAnElement(thsRng, baseTy, uTmp);
      BitOR;
    END;
    IF uTmp # invalid THEN FreeTemp(uTmp) END;
  END WordSetConstructor;

 (* ---------------------------------------------------- *)

  PROCEDURE BigSetIncl(incl : BOOLEAN); 
   (* Stack is designator address, then the   *)
   (* value to be included is on top of stack *)
    VAR tix : TempIndex;
  BEGIN
    tix  := newTemp(PointerTo(cards));
    MakeTemp(tix);                      (* dstAdr, ord              *)
   (*
    *  Compute the index of the word that
    *  holds the bit in question, then the 
    *  offset of the word in the address space 
    *  offset = (ord DIV bitsInWord) * bytesInWord
    *)
    PushCrd(bitsInWord);  DivU();
    PushCrd(bytesInWord); Mul(none);
    Add(none);                          (* adr of element is on top *)
    Duplicate;
    LoadInd(word);                      (* dstAdr, dstVal,          *)
    PushCrd(1);
    PushTemp(tix);                      (* dstAdr, dstVal, ord      *)
    FreeTemp(tix);
   (*
    *  Now we compute ord MOD bitsInWord
    *  using a bit-masking operation.
    *)
    PushCrd(bitsInWord - 1); BitAND;
    LShift;
    IF incl THEN BitOR ELSE NegBits; BitAND END;
    StoreInd(word);
  END BigSetIncl;

  PROCEDURE BigSetConstructor(expr : ExprDesc;
        		      size : CARDINAL;
        		      pop  : BOOLEAN);
  (* pre  : destination address is on top of stack *)
  (* post : set is constructed, optional pop by 1  *)
    VAR rngCrs : ElemPtr;
        thsRng : RangeDesc;
        baseTy : TypeDesc;
        uTmp   : TempIndex;       (* temporary for selector *)
        dTmp   : TempIndex;       (* temporary for dst addr *)
  BEGIN
    Assert(NOT IsEmpty(expr^.rangeSeq));
    baseTy := expr^.exprType^.baseType;
    uTmp   := newTemp(PointerTo(cards));
    dTmp   := newTemp(PointerTo(adrs));
    MakeTemp(dTmp);             (* ... dst& or dst&,dst& *)
    InitCursor(expr^.rangeSeq,rngCrs);
    PushCrd(size);              (* ==> size in words     *)
    RtsHelper(clr); 		(* args are (dst&, elNm) *)
    WHILE NOT Ended(rngCrs) DO
      GetNext(rngCrs,thsRng);
      WITH thsRng^ DO
        PushTemp(dTmp);
        IF upper = NIL THEN (* single element *)
          PushExprValue(lower);
          IF rangeTests IN lower^.testFlags THEN
            Test(baseTy, lower^.exprType); (* dst,src *)
          END;
          BigSetIncl(TRUE); 	(* args are (dst&, elNm) *)
        ELSE (* a range *)
          PushExprValue(upper);
          IF rangeTests IN upper^.testFlags THEN
            Test(baseTy,upper^.exprType); (* dst,src *)
          END;
          StoreTemp(uTmp);
         (* ----------------- *)
          PushExprValue(lower);
          IF rangeTests IN lower^.testFlags THEN
            (* the lower bound is checked against upper *)
            VariableCheck(uTmp, baseTy^.minRange);  (* CHECK THIS *)
          END;
          PushTemp(uTmp);
          RtsHelper(setRngIncl); (* args are dst&,loV,hiV *)
         (* ----------------- *)
        END;
      END; (* with *)
    END; (* while *)
    IF NOT pop THEN PushTemp(dTmp) END;
  END BigSetConstructor;

  PROCEDURE MkSetAndPushAdr(exp : ExprDesc;   (* set expression to be built *)
        	            siz : CARDINAL;   (* number of words in the set *)
                            tmp : TempIndex); (* temporary index offered up *)
    VAR class : ExprNodeClass;
        rTmp  : TempIndex;
    (* post : the set is formed, adr is pushed on eval stack *)
  BEGIN
    class := exp^.exprClass;
    IF class IN setBinops THEN
      (*
       *  Evaluate the operands, then push the addresses.
       *)
      rTmp := newTemp(exp^.exprType);
      Assert(tmp # invalid);
      PushTempAdr(tmp);
      Duplicate;
      MkSetAndPushAdr(exp^.leftOp, siz, tmp);	(* must do left first *)
      MkSetAndPushAdr(exp^.rightOp, siz, rTmp);	(* must do right next *)
      PushCrd(siz);
      (*
       *  Params for setops are (dst&,lhs&,rhs&,elNm)
       *)
      CASE class OF
        | plusNode  : RtsHelper(cup3); 
        | minusNode : RtsHelper(dif3); 
        | starNode  : RtsHelper(cap3); 
        | slashNode : RtsHelper(xor3); 
      END;
      FreeTemp(rTmp);
    ELSIF class = setDesigNode THEN
      PushTempAdr(tmp);
      BigSetConstructor(exp, siz, FALSE);
    ELSIF class = funcDesigNode THEN
      PushTempAdr(tmp);
      PushFunctionValue(exp, exp^.paramSeq);
      StoreObj(exp^.exprType);
    ELSIF class = preconNode THEN
      StatementSeq(exp^.evalLst, 0);
      MkSetAndPushAdr(exp^.theCall, siz, tmp);
    ELSE 
      PushExprAddress(exp);
    END;
  END MkSetAndPushAdr;

 (* ---------------------------------------------------- *)

  PROCEDURE DoParams(pType : TypeDesc;
        	     seq   : Sequence;
                 VAR pNum  : CARDINAL;
                 VAR list  : TempList);

    VAR pCurs   : ElemPtr;
        oSeq    : Sequence;  (* Sequence of ParInfo  *)
        nextPar : ParInfo;
   (* ------------------------------------------------------- *)
    PROCEDURE PushNextParam(elem : ParInfo;   (* the actual to be pushed *)
                        VAR pNum : CARDINAL;  (* counter for VM elements *)
                        VAR list : TempList);
     (* --------------------------------------------------- *)
      PROCEDURE PushOpenSize(desig : ExprDesc; elTyp : TypeDesc);
        VAR elem : TypeDesc;
      BEGIN
        PushOpenCount(desig);
        elem := elTyp^.elementType;
        WHILE (elem^.tyClass = arrays) AND elem^.isDynamic DO
          elem := elem^.elementType;
        END;
        IF elem^.size > 1 THEN PushCrd(elem^.size); Mul(none) END;
      END PushOpenSize;
     (* --------------------------------------------------- *)
      PROCEDURE PushValueclassActual(exp : ExprDesc; 
                                     fTp : TypeDesc);
      BEGIN
        PushExprAddress(exp); LoadObj(fTp);
      END PushValueclassActual;
     (* --------------------------------------------------- *)
      PROCEDURE PushScalarActual(exp : ExprDesc; 
                                 cls : TyNodeClass;
                                 fTp : TypeDesc);
      BEGIN
        IF fTp^.tyClass = hInts THEN
          PushLongValue(exp);
        ELSIF (fTp^.tyClass = floats) AND (cls = RR) THEN
          PushRR(exp, float);
        ELSE
          PushExprValue(exp);
          IF rangeTests IN exp^.testFlags THEN 
            Test(fTp, exp^.exprType); (* dst,src *)
          END;
        END;
      END PushScalarActual;
     (* --------------------------------------------------- *)
      PROCEDURE CopyElemByElem(expr : ExprDesc; 
                               frmT : TypeDesc);
        VAR sElT, dElT : TypeDesc;
            sSiz, dSiz : CARDINAL;
            sObj, dObj : Object;
            lLab       : LabelType;
            srcP, dstP, left : TempIndex; (* src,dst ptr; num left to copy *)
      BEGIN
        dElT := expr^.exprType;	(* ultimate element type *)
        sElT := expr^.actualX^.exprType^.elementType;
        WHILE sElT^.tyClass = arrays DO
          sElT := sElT^.elementType;
        END;
       (*
        *   At call, eval stack is ... dst&,dst&,src&,elNm
        *)
        left := newTemp(PointerTo(cards)); StoreTemp(left);
        srcP := newTemp(PointerTo(adrs));  StoreTemp(srcP);
        dstP := newTemp(PointerTo(adrs));  StoreTemp(dstP);
       (* --------- main loop ---------- *)
        AllocLabel(lLab);
        CommentLabel(lLab, "inline copy loop");
        PushAndPostIncTemp(dstP, dElT^.size);
        PushAndPostIncTemp(srcP, sElT^.size);
        LoadInd(baseObjOf(sElT));
        IF rangeTests IN expr^.actualX^.testFlags THEN 
          Test(dElT,sElT); (* dst,src *)
        END;
        StoreInd(baseObjOf(dElT));
        PreDecAndPushTemp(left);
        BranchTrue(lLab);
        WriteComment("end inline copy");
        FreeTemp(dstP); FreeTemp(srcP); FreeTemp(left);
       (* --------- end  loop ---------- *)
      END CopyElemByElem;
     (* --------------------------------------------------- *)
      PROCEDURE PushDesignator(desg : DesigRec;
                           VAR list : TempList);
        TYPE  FSet    = SET OF FormalClass;
        CONST statics = FSet{static, export, extern};
        VAR   temp : TempIndex;
              srcT : TypeDesc;
              mode : AccessMode;
      BEGIN
        mode := AccessModeOf(desg);
        IF (mode = directNonL) OR
           (mode = directLocl) AND (desg.variable^.varClass IN statics) THEN
          IF list = NIL THEN NewGroup(list) END;
          temp := newPinTemp(desg.variable^.varType);
          APPEND(list, temp);
          WriteComment("pinning static field");
          PushAdr(desg.variable, mode);
          StoreTemp(temp);
        END;
        Designator(desg, FALSE);
      END PushDesignator;
     (* --------------------------------------------------- *)
      PROCEDURE PushRefOfCopy(expr : ExprDesc; 
                              frmT : TypeDesc;
                          VAR list : TempList);
        VAR temp : TempIndex;
            srcT : TypeDesc;
            fixd : BOOLEAN;
            eByE : BOOLEAN;
      BEGIN
        srcT := expr^.actualX^.exprType;
        fixd := expr^.exprClass = fixedMarshallNode;
        eByE := expr^.elemByElem <> NIL;
       (*
        *   First, push the destination address
        *)
        IF fixd THEN
          IF list = NIL THEN NewGroup(list) END;
          IF eByE THEN
            temp := newBlobTypeTemp(expr^.mrshSiz);
          ELSIF (srcT^.tyClass = S1) OR (srcT^.tyClass = SS) THEN
            Assert(expr^.leftOp^.exprClass = literalNode);
            temp := newBlobTypeTemp(expr^.leftOp^.conValue.strHigh+1);
          ELSE
            temp := newTemp(srcT);
          END;
          APPEND(list, temp);
          PushTempAdr(temp);
        ELSE
          DerefDesig(expr^.mrshPtr^.name, word);
        END;
       (*
        *   ... Duplicate, and push source address
        *)
        Duplicate;
        PushExprAddress(expr^.actualX); (* make and push? *)
       (*
        *   Now invoke the required copy operation.
        *)
        IF eByE THEN
          IF fixd THEN
            PushCrd(ORD(expr^.mrshSiz) DIV frmT^.size);
          ELSE
            PushOpenCount(expr^.actualX); (* stack ... &dst,&dst,&src,elNm *)
          END;
          CopyElemByElem(expr, frmT);
        ELSE 
          IF fixd THEN
            PushCrd(expr^.mrshSiz);       (* stack ... &dst,&dst,&src,fxSz *)
          ELSE
            PushOpenSize(expr^.actualX, srcT);
          END;
          CopyBlock(frmT^.alignMask);     (* stack ... &dst                *)
        END;
      END PushRefOfCopy;
     (* --------------------------------------------------- *)
      PROCEDURE StringToOpenArray(act : ExprDesc);
        VAR tmp : TempIndex;
      BEGIN
        tmp := newTemp(PointerTo(adrs));
        PushExprValue(act);
        MakeTemp(tmp); 
        GetVectorBlob;
        PushTemp(tmp);
        GetVectorHigh;
        IF indexTests IN act^.testFlags THEN NonNegCheck() END;
        FreeTemp(tmp);
      END StringToOpenArray;
     (* --------------------------------------------------- *)
      VAR actCls : TyNodeClass;
          actTyp : TypeDesc;
     (* --------------------------------------------------- *)
    BEGIN  (* PushNextParam *)
      WITH elem^ DO
        IF actExp^.exprClass = errNode THEN RETURN END;
        actTyp := actExp^.exprType;
        actCls := actTyp^.tyClass;
       (* -------------------------------------- *
        *       Special case code for CLR.       *
        * -------------------------------------- *)
        CASE clrMod OF
        | pushVal   :
            IF verbose IN modState THEN WriteComment("pushVal") END; 
            PushScalarActual(actExp, actCls, frmTyp); INC(pNum);
        | pushRef   :
            IF verbose IN modState THEN WriteComment("pushRef") END; 
            PushDesignator(actExp^.name, list); INC(pNum);
        | copyObj   :
            IF verbose IN modState THEN WriteComment("copyObj") END; 
            PushValueclassActual(actExp, frmTyp); INC(pNum);
        | localCopy : (* including marshalling case *)
            IF verbose IN modState THEN WriteComment("localCopy") END; 
            IF actCls = stringTs THEN
              StringToOpenArray(actExp); INC(pNum,2);
            ELSE
              PushRefOfCopy(actExp, frmTyp, list); INC(pNum);
            END;
        | refToArr : 
            IF verbose IN modState THEN WriteComment("refToArr") END; 
            IF actCls = stringTs THEN
              StringToOpenArray(actExp); INC(pNum,2);
            ELSE
              PushDesignator(actExp^.name, list); INC(pNum);
            END;
        END;
      END; (* with *)
    END PushNextParam;

  BEGIN (* DoParams *)
    GetActuals(seq, pType, oSeq);
    pNum := 0;
    InitCursor(oSeq, pCurs);
    WHILE NOT Ended(pCurs) DO
      GetNext(pCurs, nextPar);
      PushNextParam(nextPar, pNum, list);
    END;
  END DoParams;

 (* =========================================================== *)

  PROCEDURE PushFunctionValue(exp : ExprDesc;
        		      seq : Sequence);

      VAR des      : DesigRec;

      PROCEDURE CallStandardFunc(id : StandardProcs);
        VAR curs  : ElemPtr;
            par1  : ExprDesc;
            par2  : ExprDesc;
            xLab  : LabelType;
            oTest : BOOLEAN;
            rTest : BOOLEAN;
            tMode : ModeEnum;
            pType : TypeDesc; (* type desc of par  *)
            dType : TypeDesc; (* type desc of dest *)
            pCls  : TyNodeClass; (* class of par   *)
            dCls  : TyNodeClass; (* class of dest  *)
            mId   : IdDesc;
            dTmp  : TempIndex;
            rTmp  : TempIndex;
      BEGIN
        InitCursor(seq,curs);
        IF NOT Ended(curs) THEN
          GetNext(curs,par1);
          IF	(id <> valP) AND
        	(id <> minP) AND
        	(id <> maxP) THEN
            pType := par1^.exprType;
            pCls  := pType^.tyClass;
          END;
          IF NOT Ended(curs) THEN
            GetNext(curs,par2);
          END;
        END;
        CASE id OF
        | (* highP, minP, maxP,*) sizeP, tsizeP, castP : Assert(FALSE);
        | highP : (* assert: is stringT *)
            PushExprValue(par1);
            GetVectorHigh();
        | minP :
            PushHugeMin();
        | maxP :
            PushHugeMax();
        | absP :
            PushExprValue(par1);
            IF ovfloTests IN par1^.testFlags THEN 
              MinIntTest(pType^.tyClass);
            END;
            AbsVal(baseObjOf(pType));
        | capP :
            PushExprValue(par1);
            Duplicate;
            PushCrd(ORD("a"));			(* val val "a" *)
            Sub(none);				(* val exp     *)
            PushCrd(ORD("z") - ORD("a"));	(* val exp 25  *)
            CardRelop(lessEqNode);		(* val isUpper *)
            PushCrd(ORD("a") - ORD("A"));	(* val bool 32 *)
            Mul(none);				(* val 0or32   *)
            Sub(none);				(* CAP(val)    *)
        | chrP :
            PushExprValue(par1);
            MkU8(rangeTests IN par1^.testFlags);
        | floatP, lfloatP :		(* new code 20-6-91 kjg *)	
            PushExprValue(par1);
            IF pCls = subranges THEN pCls := pType^.hostType^.tyClass END;
            IF (pCls # doubles) AND (pCls # RR) THEN 
              IF NOT IsSignedType(pType) THEN MkCrd END;
              MkR64;
            END;
        | sfloatP :
            PushExprValue(par1);
            IF pCls = subranges THEN pCls := pType^.hostType^.tyClass END;
            IF pCls # floats THEN 
              IF NOT IsSignedType(pType) THEN MkCrd END;
              MkR32;
            END;
        | truncP  : 
            PushExprValue(par1);
            oTest := ovfloTests IN par1^.testFlags; 
            TruncU(oTest);
        | entierP :
            PushExprValue(par1);
            oTest := ovfloTests IN par1^.testFlags; 
            IF pCls = floats THEN FloorF(oTest);
            ELSE FloorD(oTest);
            END;
        | roundP  :
            PushExprValue(par1);
            oTest := ovfloTests IN par1^.testFlags; 
            IF pCls = floats THEN RoundF(oTest);
            ELSE RoundD(oTest);
            END;
        | htruncP, hentierP, hroundP : 
            PushExprValue(par1);
            oTest := ovfloTests IN par1^.testFlags; 
            IF pCls = floats THEN MkR64 END;
            IF id = htruncP THEN
              HTrunc(oTest);
            ELSIF id = hentierP THEN
              HEntier(oTest);
            ELSE 
              HRound(oTest);
            END;
        | oddP :
            PushExprValue(par1);
            PushCrd(1);
            BitAND;
        | ordP : 
            PushExprValue(par1);
        | intP : 
            PushExprValue(par1);
            oTest := ovfloTests IN par1^.testFlags; 
            IF  pCls = hInts  THEN MkI32(oTest);
            ELSE TruncI(oTest);
            END; 
        | hugeP : 
(* FIX ME --- fold literals using PushHuge() 
 *          PushExprValue(par1);
 *          MkI64;
 *)
	    PushExprValue(par1);
	    oTest := ovfloTests IN par1^.testFlags; 
	    IF pCls = floats THEN
	      MkR64; HTrunc(oTest)
	    ELSIF (pCls = doubles) OR (pCls = RR) THEN
	      HTrunc(oTest)
	    ELSIF IsSignedType(pType) OR (pCls = ZZ) THEN
	      ConvItoI64;
	    ELSE
	      ConvUtoI64;
	    END;
        | valP :
            PushExprValue(par2);
            pType := par2^.exprType;
            pCls  := pType^.tyClass;
            dType := par1^.name.variable^.typType;
            dCls  := dType^.tyClass;
            oTest := ovfloTests IN par2^.testFlags; 
            rTest := rangeTests IN par2^.testFlags; 
            IF pCls = subranges THEN pCls := pType^.hostType^.tyClass END;
            IF dCls = subranges THEN dCls := dType^.hostType^.tyClass END;
           (*
            *   two dimensional case analysis
            *)
           (* --------- param must be real64 ---------- *)
            IF pCls = doubles THEN
              IF dCls = doubles THEN (* skip *)
              ELSIF dCls = floats THEN MkR32;
              ELSE (* dest is an integral type *)
        	IF dCls = ints THEN 
                  MkI32(oTest);
                  IF rTest AND (dType^.tyClass = subranges) THEN
                    Test(dType, PointerTo(ints)); (* dst,src *)
                  END;
        	ELSIF dCls = hInts THEN 
                  (* MkI64; *)
                  HTrunc(oTest);
        	ELSE 
                  MkU32(oTest);
                  IF rTest AND (dType^.tyClass = subranges) THEN
                    Test(dType, PointerTo(cards)); (* dst,src *)
                  END;
        	END;
              END;
           (* --------- param must be real32 ---------- *)
            ELSIF pCls = floats THEN
              IF dCls = doubles THEN MkR64;
              ELSIF dCls = floats THEN (* skip *)
              ELSE (* dest is an integral type *)
        	IF dCls = ints THEN 
                  MkI32(oTest);
                  IF rTest AND (dType^.tyClass = subranges) THEN
                    Test(dType, PointerTo(ints)); (* dst,src *)
                  END;
        	ELSIF dCls = hInts THEN 
                  (* MkI64; *)
                  HTrunc(oTest);
        	ELSE 
                  MkU32(oTest);
                  IF rTest AND (dType^.tyClass = subranges) THEN
                    Test(dType, PointerTo(cards)); (* dst,src *)
                  END;
        	END;
              END;
           (* --------- param must be int32  ---------- *)
            ELSIF pCls = ints THEN
              IF    dCls = doubles THEN MkR64;
              ELSIF dCls = floats  THEN MkR32;
              ELSIF dCls = hInts   THEN ConvItoI64;
              ELSIF rTest AND (dType^.tyClass = subranges) THEN
                Test(dType, PointerTo(ints)); (* dst,src *)
              END;
           (* --------- param must be int64  ---------- *)
            ELSIF pCls = hInts THEN
              IF    dCls = doubles THEN MkR64;
              ELSIF dCls = floats  THEN MkR32;
              ELSIF dCls = ints    THEN
                MkI32(oTest);
                IF rTest AND (dType^.tyClass = subranges) THEN
                  Test(dType, PointerTo(ints)); (* dst,src *)
                END;
              ELSE (* do a cardinal conversion *)
        	MkU32(oTest);
                IF rTest AND (dType^.tyClass = subranges) THEN
                  Test(dType, PointerTo(cards)); (* dst,src *)
                END;
              END;
           (* --------- param must be uint32 ---------- *)
            ELSE (* IF pCls = cards THEN *)
              IF    dCls = doubles THEN MkCrd; MkR64;
              ELSIF dCls = floats  THEN MkCrd; MkR32;
              ELSIF dCls = hInts   THEN ConvUtoI64;
              ELSIF rTest AND (dType^.tyClass = subranges) THEN
                Test(dType, PointerTo(cards)); (* dst,src *)
              END;
            END;  
           (* ------- end of 2-dimensional case ------- *)
        | lengthP : 
            IF pCls = stringTs THEN       (* stringTs have only a single  *)
              dTmp := newTemp(par1^.exprType);
              PushExprValue(par1);        (* param, and the HIGH is found *)
              MakeTemp(dTmp);             (* internally from the struct.  *)
              GetVectorBlob;              (* ... &dat                     *)
              PushTemp(dTmp);             (* ... &dat,&vc                 *)
              GetVectorHigh;              (* ... &dat,high                *)
              FreeTemp(dTmp);
            ELSIF par1^.exprClass = desigNode THEN
              Designator(par1^.name, FALSE);
              PushExprValue(par2);
            ELSE
              dTmp := newTemp(par1^.exprType);
              MkObjAndPushAdr(par1, dTmp);
              PushExprValue(par2);
              FreeTemp(dTmp);
            END;
           (*
            *   The strLen function takes two params:
            *   the first is a pointer to the "string" value,
            *   the second is the high of the containing array.
            *   The function returns length or high, whichever
            *   is found sooner.
            *)
            RtsHelper(strLen);
        | adrP :
            PushExprAddress(par1);
        | difAdrP : 
            PushExprValue(par1);
            PushExprValue(par2);
            Sub(none);
        | addAdrP, subAdrP :
            DerefDesig(par1^.name,word);
            PushExprValue(par2);
            IF id = addAdrP THEN
              Add(none);
            ELSE 
              Sub(none);
            END;
        | timeP : 
            MkTrap(timeTrp);
        | shiftP, rotateP :
            PushExprValue(par1);
            IF id = shiftP THEN
              IF par2^.exprClass # literalNode THEN
                PushExprValue(par2);
                Shift;
              ELSIF par2^.conValue.intValue > 0 THEN
                PushInt(par2^.conValue.intValue); 
                LShift;
              ELSIF par2^.conValue.intValue < 0 THEN
                PushInt(-par2^.conValue.intValue);
                RShift;
             (* ELSE stack value is correct already *)
              END;
            ELSE
              dTmp := newTemp(par1^.exprType);    (* lhs value   *)
              MakeTemp(dTmp);
              IF par2^.exprClass # literalNode THEN
                rTmp := newTemp(par1^.exprType);  (* rhs MOD(32) *)
                PushExprValue(par2);
                PushCrd(bitsInWord-1);
                BitAND;
                MakeTemp(rTmp);
                LShift;
                PushTemp(dTmp);
                PushCrd(bitsInWord);
                PushTemp(rTmp);
                Sub(none);
                FreeTemp(rTmp);
              ELSE
                PushCrd(par2^.conValue.fixValue MOD 32);
                LShift;
                PushTemp(dTmp);
                PushCrd(32 - par2^.conValue.fixValue MOD 32);
              END;
              LRShift;
              BitAND;
              FreeTemp(dTmp);
            END;
        END;
      END CallStandardFunc;

    VAR typ  : TypeDesc;
        pVar : BOOLEAN;
        pNum : CARDINAL;
        list : TempList;

  BEGIN
      des := exp^.name;
      (*
       *  first must check here for standard procs
       *)
      IF  des.variable^.idClass = stFunc THEN
        CallStandardFunc(des.variable^.procVal);
      ELSE (* now the actual call *)
        pVar := des.variable^.idClass = varNode;
        IF pVar THEN (* proc var ... *)
          typ := typeOfDes(des);
          (* ... and there is no static link *)
        ELSE 
          typ := des.variable^.procType;
          PushStaticLink(des.variable);
        END;
        list := NIL;
        DoParams(typ, seq, pNum, list); 
        IF pVar THEN
          DerefDesig(des, word);
          CallTos(typ, pNum, 1, FALSE);
        ELSE 
          CallMth(des.variable, pNum, 1);
        END;
        FreeGroup(list);  (* MUST COME AFTER CALL *)
      END;
  END PushFunctionValue;

 (* =========================================================== *)

  PROCEDURE PushLongValue(op : ExprDesc);
  BEGIN
    PushExprValue(op);
    IF op^.exprClass = literalNode THEN 
      IF op^.exprType^.tyClass = UU THEN ConvUtoI64 ELSE ConvItoI64 END;
    END;
  END PushLongValue;

  PROCEDURE PushRR(exp : ExprDesc; obj : Object);
 (*
  * This function reflects the changes to FixLiteral()
  * 0.0 is marked and not put on the literal chain 
  * otherwise floats are stuck in after the double literal
  * (* jl Jun 94 *)
  *)
  BEGIN
    IF exp^.rtOffset = literalZero THEN
      PushZero(obj);
    ELSIF obj = double THEN
      PushCon(exp^.rtOffset);
      LoadInd(double);
    ELSE (* shorten literal at compile time *)
      PushCon(exp^.rtOffset + bytesInReal); (* jl Jun 94 *)
      LoadInd(float);
    END;
  END PushRR;

  PROCEDURE PushExprValue(exp : ExprDesc);
  (* pre  : exp^ is a word sized or less object, or a REAL *)
    VAR tLab, fLab, xLab : LabelType;
        class  : TyNodeClass;
        sClass : TyNodeClass;
        objt   : Object;
        size   : CARDINAL;
        sSize  : CARDINAL;
        tix    : TempIndex;
        dTmp   : TempIndex;
        dType  : TypeDesc;
        set    : LexAttType;
        indx   : INTEGER;
        litValue : CARDINAL;
        sign, doTest, lit, huge : BOOLEAN;
  BEGIN
    WITH exp^ DO
      class := exprType^.tyClass;	(* not always what is needed *)
      CASE exprClass OF
      | preconNode :
          StatementSeq(evalLst,0);
          PushExprValue(exp^.theCall);
      | selConstNode : 
          ConstDesignator(exp); 
          objt := baseObjOf(exprType);
          LoadInd(objt);
      | adrDesigNode : 
          Designator(name, FALSE); 
      | desigNode : 
          (*
           *  if the designator is some procedure name
           *  or if this is an adrDesigNode then
           *  the designator address _is_ the value
           *)
          IF  NOT (name.variable^.idClass IN procSet) THEN
          (*
           *  here, by convention, the expression type might
           *  be different from the designator type (i.e. an
           *  index type). In this case, the object to deref
           *  must be deduced from the designator ...
           *)
            dType := typeOfDes(name);
            objt  := baseObjOf(dType);
            DerefDesig(name, objt); 
          ELSE (* proc vars *)
            Designator(name, FALSE); 
          END;
      | castNode :
         (*
          *  structure:
          *	source  : ExprDesc  -- points to source expression
          *	needTmp : BOOLEAN   -- does this case need a temp
          *	wrd2wrd : BOOLEAN   -- a possibly shortening cast
          *	tempId  : IdDesc    -- name of temporary variable
          *     exprType : TypeDesc -- destination type descriptor
          *)
          sSize  := source^.exprType^.size;
          sClass := source^.exprType^.tyClass;
          IF needsCopy(sClass, sSize) THEN
            IF sClass = SS THEN
              PushExprAddress(source);
            ELSIF needTmp THEN
              dTmp := newTemp(source^.exprType);
	      PushAdr(tempId, directLocl);
              Duplicate;
              MkObjAndPushAdr(source, dTmp);
              IF sClass <> SS THEN
                PushCrd(sSize);				(* source size *)
              ELSIF source^.conValue.strHigh >= exprType^.size THEN
                PushCrd(exprType^.size);		(* dest size   *)
              ELSE
                PushCrd(source^.conValue.strHigh + 1);  (* string size *)
              END;
              CopyBlock(source^.exprType^.alignMask);
            ELSE
              dTmp := newTemp(source^.exprType);
              MkObjAndPushAdr(source, dTmp);
              FreeTemp(dTmp);
            END;
	    LoadInd(baseObjOf(exprType));
            (* this leaves *pointer* to value on the stack *)
          ELSIF needTmp THEN
            PushAdr(tempId, directLocl);
            PushExprValue(source);
            IF wrd2wrd THEN 
              StoreInd(baseObjOf(exprType));
            ELSE 
              StoreInd(baseObjOf(source^.exprType));
            END;
            PushAdr(tempId,directLocl);
            LoadInd(baseObjOf(exprType));
          ELSE 
            PushExprValue(source);
          END;
      | funcDesigNode :
          PushFunctionValue(exp, paramSeq);
      | setDesigNode :
          WordSetConstructor(exp);
      | literalNode : 
          IF (class = chars) OR
             (class = S1) THEN 
            PushCrd(ORD(conValue.charValue));
          ELSIF class = sets THEN (* assert: word set *)
            FOR size := 0 TO bytesInWord - 1 DO
              IF bigEndian THEN
                set.bytes[bytesInWord - 1 - size] :=
        			StringTable(conValue.patternIx + size);
              ELSE
                set.bytes[size] := StringTable(conValue.patternIx + size);
              END;
            END;
            PushCrd(set.fixValue);
          ELSIF class = RR THEN
            PushRR(exp, double);
          ELSE PushInt(conValue.intValue);
          END;
      | negateNode :
          PushLongValue(notOp);
          IF ovfloTests IN testFlags THEN MinIntTest(class) END;
          Neg;
      | inNode :
          tix  := invalid;
          dTmp := invalid;
          size := rightOp^.exprType^.size;
         (*
          *  note the use of unsigned tests here to catch
          *  (perhaps) signed values which are beyond either 
          *  end of the range of the base type of the set.
          *)
          IF leftOp^.exprClass = literalNode THEN
            litValue := leftOp^.conValue.fixValue;
            IF litValue > MaxOfOrdType(rightOp^.exprType^.baseType) THEN
              PushCrd(0);
            ELSE
              IF size <= bytesInWord THEN
        	PushExprValue(rightOp);
              ELSE
                dTmp := newTemp(rightOp^.exprType);
                MkSetAndPushAdr(rightOp, size DIV bytesInWord, dTmp);
                IF litValue >= bitsInWord THEN
                  AddOffset((litValue DIV bitsInWord) * bytesInWord);
                END;
                LoadInd(word);
              END;
              PushCrd(litValue MOD bitsInWord);
              SetInOp();
            END;
          ELSIF (rangeTests IN leftOp^.testFlags) THEN
            tix  := newTemp(PointerTo(cards));
           (*
            *  It is the left operand which carries the information
            *  as to whether an out of range left operand can occur
            *)
            PushExprValue(leftOp);
            MakeTemp(tix);
            PushCrd(MaxOfOrdType(rightOp^.exprType^.baseType));
            CardRelop(lessEqNode);      (* true ==> in range *)
            IF size <= bytesInWord THEN (* a word sized set  *)
              PushExprValue(rightOp);   (* rhs *)
              PushTemp(tix);            (* lhs *)
            ELSE
              dTmp := newTemp(rightOp^.exprType);
              Neg;		(* turn true/false into 111.../000...*)
              Duplicate;
              PushTemp(tix);		(* lhs *)
              BitAND;
              StoreTemp(tix); 
             (*
              *  the temporary now has an in-range index or zero
              *)
              MkSetAndPushAdr(rightOp, size DIV bytesInWord, dTmp);
              PushTemp(tix);		(* modified index *)
              PushCrd(bitsInWord);  DivU();
              PushCrd(bytesInWord); Mul(none); (* == lOp DIV 32 * 4 *)
              Add(none);
              LoadInd(word);
              PushTemp(tix);		       (* modified index *)
              PushCrd(bitsInWord - 1); BitAND; (* == lOp MOD 32  *)
            END;
            SetInOp;
            BitAND;
          ELSE (* variable lhs, but no range test... *)
            IF size <= bytesInWord THEN
              PushExprValue(rightOp);   (* rhs *)
              PushExprValue(leftOp);    (* lhs *)
            ELSE
              tix  := newTemp(PointerTo(cards));
              dTmp := newTemp(rightOp^.exprType);
              MkSetAndPushAdr(rightOp, size DIV bytesInWord, dTmp);
              PushExprValue(leftOp);
              MakeTemp(tix);
              PushCrd(bitsInWord);  DivU();
              PushCrd(bytesInWord); Mul(none); (* == lOp DIV 32 * 4 *)
              Add(none);
              LoadInd(word);
              PushTemp(tix);
              PushCrd(bitsInWord - 1); BitAND; (* == lOp MOD 32     *)
            END;
            SetInOp;
          END;
          IF tix # invalid THEN FreeTemp(tix) END;
          IF dTmp # invalid THEN FreeTemp(dTmp) END;
      | equalsNode .. lessEqNode :
          (* sub exps are not necessarily word sized *)
          IF rightOp^.exprType^.tyClass = sets THEN
            size := rightOp^.exprType^.size;
            IF size > bytesInWord THEN (* big set *)
              tix  := newTemp(rightOp^.exprType);
              dTmp := newTemp(rightOp^.exprType);
              MkSetAndPushAdr(leftOp, size DIV bytesInWord, tix);
              MkSetAndPushAdr(rightOp, size DIV bytesInWord, dTmp);
              PushCrd(size DIV bytesInWord);
              BigSetRelop(exprClass);    (* args are (lOp&,rOp&,elNm) *)
              FreeTemp(tix);
              FreeTemp(dTmp);
            ELSE (* a word-sized set *)
              PushExprValue(leftOp);
              PushExprValue(rightOp);
              SetRelop(exprClass);
            END;
          ELSE (* not a set *)
            class  := leftOp^.exprType^.tyClass;
            IF class = RR THEN class := rightOp^.exprType^.tyClass END;
            PushExpAsTyClass(leftOp, class);
            PushExpAsTyClass(rightOp, class);
            IF class IN realClasses THEN
              FltRelop(exprClass);
            ELSIF (leftOp^.exprClass <> literalNode) AND
        	   IsSignedType(leftOp^.exprType) OR
            	   IsSignedType(rightOp^.exprType) THEN 
              IntRelop(exprClass);
            ELSE 
              CardRelop(exprClass);
            END;
          END;
      | andNode :
         (*
          *  Code pattern is 
          *       <eval lOp and branch on false> 
          *       <eval rOp and branch on false> 
          *  // both are true
          *       push 1
          *       br xLab
          *  fLab:
          *       push 0
          *  xLab:
          *)
          AllocLabel(fLab); 
          AllocLabel(xLab); 
          FallTrue(leftOp, fLab);
          FallTrue(rightOp, fLab);
          PushCrd(1);
          Branch(xLab);
          CodeLabel(fLab);
          PushCrd(0);
          CodeLabel(xLab);
      | orNode :
         (*
          *  Code pattern is 
          *       <eval lOp and branch on true> 
          *       <eval rOp and branch on true> 
          *  // both are false
          *       push 0
          *       br xLab
          *  fLab:
          *       push 1
          *  xLab:
          *)
          AllocLabel(tLab); 
          AllocLabel(xLab); 
          FallFalse(leftOp, tLab);
          FallFalse(rightOp, tLab);
          PushCrd(0);
          Branch(xLab);
          CodeLabel(tLab);
          PushCrd(1);
          CodeLabel(xLab);
      | notNode : 
          PushExprValue(notOp);
          NegBool;
      ELSE (* is some other binop *)
        PushExpAsTyClass(leftOp, class);
        PushExpAsTyClass(rightOp, class);
        IF class = sets THEN
          Assert(exprType^.size = bytesInWord);
          CASE exprClass OF 
          | plusNode  : BitOR;
          | starNode  : BitAND;
          | slashNode : BitXOR;
          | minusNode : NegBits; BitAND;
          END;
        ELSIF class IN realClasses THEN
          CASE exprClass OF
          | starNode    : Mul(none);
          | plusNode    : Add(none);
          | minusNode   : Sub(none);
          | slashNode   : Slash(none);
          END;
        ELSE
          doTest := (ovfloTests IN testFlags);
          sign := IsSignedType(exprType);
          CASE exprClass OF
          | starNode    : Mul(addMode[sign,doTest]);
          | plusNode    : Add(addMode[sign,doTest]);
          | minusNode   : Sub(addMode[sign,doTest]);
          | slashNode   : Slash(divMode[sign,doTest]);
          | remNode     : 
              huge := class = hInts;
              IF huge THEN
        	RemH();
              ELSIF NOT sign THEN
                RemU();
              ELSE
                RemI();
              END;
          | divNode, modulusNode : 
              huge := class = hInts;
              IF doTest AND sign AND NOT huge AND
                  (rightOp^.exprClass <> literalNode) THEN ModTest(class) END;
              IF sign AND (rightOp^.exprClass = literalNode) AND
                                        (rightOp^.conValue.intValue > 0) THEN 
                indx := rightOp^.conValue.intValue; 
                AllocLabel(xLab); 
        	IF exprClass = divNode THEN 
        	 (* Do correction if necessary, then divide *)
                  Pop; (* damn! *)
                  Duplicate;
                  IF huge THEN PushHuge(0) ELSE PushInt(0) END;
                  IntRelopTrue(grEqualNode, xLab);
                  IF huge THEN PushHuge(HUGE(indx-1)) ELSE PushInt(indx-1) END;
                  Sub(none);
                  CodeLabel(xLab);
                  IF huge THEN PushHuge(HUGE(indx)) ELSE PushInt(indx) END;
                  Slash(intV);
        	ELSE  (* Do remainder, then correction step if necessary *)
                  RemI;
                  Duplicate;
                  IF huge THEN PushHuge(0) ELSE PushInt(0) END;
                  IntRelopTrue(grEqualNode, xLab);
                  IF huge THEN PushHuge(HUGE(indx)) ELSE PushInt(indx) END;
                  Add(none);
                  CodeLabel(xLab);
        	END;
              ELSIF NOT sign THEN
        	IF exprClass = divNode THEN DivU() ELSE ModU() END;
              (* ELSE  do it the hard way *)
              ELSIF huge THEN
        	IF exprClass = divNode THEN DivH() ELSE ModH() END;
              ELSE 
        	IF exprClass = divNode THEN DivI() ELSE ModI() END;
              END;
          END;
        END;
      END; (* outer case *)
    END; (* with *)
  END PushExprValue;

  PROCEDURE PushExpAsTyClass(exp : ExprDesc; cls : TyNodeClass);
  BEGIN
    IF (cls = floats) AND 
       (exp^.exprType^.tyClass = RR) THEN PushRR(exp, float);
    ELSIF cls = hInts THEN 
      PushLongValue(exp);
    ELSE
      PushExprValue(exp);
    END;
  END PushExpAsTyClass;

  PROCEDURE StatementSeq(seq : Sequence;   (* the stat-seq    *)
                         lab : LabelType); (* opt. loop label *)

    CONST linMax = 3;	(* max. number of cases expanded linearly *)

    VAR cursor : ElemPtr;
        stmnt  : StatDesc;
        class  : TyNodeClass;
        object : Object;
        length : CARDINAL;
        align  : CHAR;
        lLab   : LabelType; (* loop front label *)
        xLab   : LabelType; (* loop exit label  *)

    PROCEDURE LinearTests(str   : CaseString; 		(* the range-string  *)
        		  lo,hi : INTEGER;		(* indices in string *)
        		  tMin  : INTEGER;		(* min value of exp. *)
        		  tMax  : INTEGER;		(* max value of exp. *)
        		  tmp   : TempIndex;		(* temporary indes   *)
        		  def   : LabelType);		(* default label     *)
      VAR sIx : INTEGER;
          nxt : LabelType;
          min : INTEGER;
          max : INTEGER;
          sng : BOOLEAN;
    BEGIN
     (*
      *  Assert : value at runtime will always be in [tMin .. tMax]
      *)
      FOR sIx := lo TO hi DO
        min := str[sIx].min; 
        max := str[sIx].max;
        sng := (min = max);
        nxt := str[sIx].cas^.theLabel;
        IF (tMin < min) AND (max < tMax) THEN	(* [tMin-----------tMax] *)
          PushTemp(tmp);			(*     [min---max]       *)
          PushInt(min);
          IF sng THEN (* singleton *)
            CardRelopTrue(equalsNode, nxt);
          ELSE (* a range *)
            Sub(none); PushInt(max-min);
            CardRelopTrue(lessEqNode, nxt);
          END;
        ELSIF tMin < min THEN			(* [tMin-----------tMax] *)
          PushTemp(tmp);			(*           [min---max] *)
          PushInt(min);
          IF sng THEN 
            CardRelopTrue(equalsNode, nxt);
          ELSE 
            IntRelopTrue(grEqualNode, nxt);
          END;
          tMax := min - 1;
        ELSIF max < tMax THEN			(* [tMin-----------tMax] *)
          PushTemp(tmp);			(* [min---max]           *)
          PushInt(max);
          IF sng THEN 
            CardRelopTrue(equalsNode, nxt);
          ELSE 
            IntRelopTrue(lessEqNode, nxt);
          END;
          tMin := max + 1;
        ELSE					(* [tMin-----------tMax] *)
          Branch(nxt);				(* [min-------------max] *)
          tMax := min - 1;
        END;
      END; (* for *)
      IF tMin <= tMax THEN Branch(def) END;
    END LinearTests;

    PROCEDURE DoDispatch(str   : CaseString;
        		 lo,hi : INTEGER;
        		 tmp   : TempIndex;
        		 def   : LabelType);
      VAR mnVal : INTEGER;
          tbSiz : INTEGER;
          locat : LabelType;
          tbPtr : JumpTabDesc;
          strIx, selIx, tabIx : INTEGER;
    BEGIN
     (*
      *  Assert : value at runtime will always be in
      *		  [str[lo].min .. str[hi].max]
      *)
      PushTemp(tmp);
      mnVal := str[lo].min;
     (*
      *  generate the jump code
      *)
      tbSiz := str[hi].max - mnVal + 1;
      IF mnVal <> 0 THEN
        PushInt(mnVal);
        Sub(none);
      END;
      CreateJumpTable(tbSiz, tbPtr);
     (*
      *  build the jump table
      *  in a memory buffer from the heap
      *)
      tabIx := 0;
      selIx := str[lo].min;
      FOR strIx := lo TO hi DO
        WHILE selIx < str[strIx].min DO
          tbPtr^.elems[tabIx] := def;
          INC(tabIx); INC(selIx);
        END;
        locat := str[strIx].cas^.theLabel;
        WHILE selIx <= str[strIx].max DO
          tbPtr^.elems[tabIx] := locat;
          INC(tabIx); INC(selIx);
        END;
      END;
      Switch(tbPtr);
    END DoDispatch;

    PROCEDURE PartTests(str   : CaseString;	(* the cases string    *)
        		prt   : PartString;	(* the partition str.  *)
        		lo,hi : INTEGER;	(* range of part. tab. *)
        		tyMin : INTEGER;	(* value range minimum *)
        		tyMax : INTEGER;	(* value range maximum *)
        		tmp   : TempIndex;	(* index of temp value *)
        		def   : LabelType);	(* default label ord.  *)
      VAR mid   : INTEGER;			(* mid-pt of part rng. *)
          minIx : INTEGER;			(* min caseStr index   *)
          maxIx : INTEGER;			(* max caseStr index   *)
          mnVal : INTEGER;			(* min value of range  *)
          mxVal : INTEGER;			(* max value of range  *)
          loLab : LabelType;			(* label for val<this  *)
          hiLab : LabelType;			(* label for val>this  *)
    BEGIN
      IF hi < lo THEN Branch(def); RETURN END;  (* SKIP: NO PARTITIONS *)
      mid := (lo + hi) DIV 2;
      (* do this partition *)
      minIx := prt[mid].nIx;
      maxIx := prt[mid].xIx;
      mnVal := str[minIx].min;
      mxVal := str[maxIx].max;
      IF lo < mid THEN AllocLabel(loLab) ELSE loLab := def END;
      IF mid < hi THEN AllocLabel(hiLab) ELSE hiLab := def END;
      IF (loLab = hiLab) AND
         (mnVal > tyMin) AND 
         (mxVal < tyMax) THEN   (* optimize dbl-ended *)
        PushTemp(tmp);
        IF mnVal = mxVal THEN   (* equality test here *)
          PushInt(mnVal);
          CardRelopTrue(notEqNode, loLab);
        ELSE
          IF mnVal <> 0 THEN PushInt(mnVal); Sub(none) END;
          PushInt(mxVal - mnVal);  (* lit <> 0! *)
          CardRelopTrue(greaterNode, loLab);
        END;
      ELSE
        IF mnVal > tyMin THEN (* test for low bound *)
          PushTemp(tmp);
          PushInt(mnVal);
          IntRelopTrue(lessNode, loLab);
        END;
        IF mxVal < tyMax THEN (* test for high bound *)
          PushTemp(tmp);
          PushInt(mxVal);
          IntRelopTrue(greaterNode, hiLab);
        END;
      END;
      (* now do this partition *)
      IF maxIx = minIx THEN			(* singleton range only *)
        Branch(str[maxIx].cas^.theLabel);
      ELSIF maxIx - minIx < linMax THEN
        LinearTests(str, minIx, maxIx, mnVal, mxVal, tmp, def);
      ELSE
        DoDispatch(str, minIx, maxIx, tmp, def); (* with no bounds check *)
      END;
      (* now emit the others recursively *)
      IF lo < mid THEN
        Assert(mnVal > tyMin);
        CodeLabel(loLab); 
        PartTests(str, prt, lo, mid-1, tyMin, (mnVal-1), tmp, def);
      END;
      IF mid < hi THEN
        Assert(mxVal < tyMax);
        CodeLabel(hiLab); 
        PartTests(str, prt, mid+1, hi, (mxVal+1), tyMax, tmp, def);
      END;
    END PartTests;

    PROCEDURE EncodeCase(stat : StatDesc);
      VAR casCurs    : ElemPtr;
          thisCase   : CaseDesc;
          defLabel   : LabelType;	(* label of default *)
          exitLabel  : LabelType;	(* case exit label  *)
          location   : LabelType;	(* current label    *)
          minValue   : INTEGER;
          maxValue   : INTEGER;
          selTmp     : CARDINAL;
          selTyp     : TypeDesc;
    BEGIN
      WITH stat^ DO
       (*
        *  Assert: selector consts are all in the integer range.
        *
        *  Allocate some labels.
        *)
        AllocLabel(exitLabel);
        AllocLabel(defLabel);
        InitCursor(cases, casCurs);
        WHILE NOT Ended(casCurs) DO
          GetNext(casCurs, thisCase);
          AllocLabel(location);
          thisCase^.theLabel := location;
        END;
        selTyp := caseInfo^.switch^.exprType;
        selTmp := newTemp(selTyp);
        PushExprValue(caseInfo^.switch);
        StoreTemp(selTmp);
       (*
        *  First, compute the value limits.
        *)
        (* $R- *)
        minValue := MinOfOrdType(caseInfo^.switch^.exprType);
        maxValue := MaxOfOrdType(caseInfo^.switch^.exprType);
        IF minValue > maxValue THEN (* type has wrapped *)
          minValue := MIN(INTEGER); maxValue := MAX(INTEGER);
        END;
        (* $R= *)
        PartTests(caseInfo^.caseStr,caseInfo^.partStr,
        		0,HIGH(caseInfo^.partStr),
        		minValue,maxValue,selTmp,defLabel);
       (*
        *  Now, emit the code for all cases
        *)
        InitCursor(cases, casCurs);
        WHILE NOT Ended(casCurs) DO
          GetNext(casCurs, thisCase);
          CodeLabel(thisCase^.theLabel);
          StatementSeq(thisCase^.statSeq, lab);
          Branch(exitLabel);
        END;
       (*
        *  emit the default code
        *)
        CodeLabel(defLabel);
        IF IsEmpty(default) THEN 
          PushTemp(selTmp);
          IF IsSignedType(selTyp) THEN
            MkTrap(casTrpI);
          ELSE
            MkTrap(casTrpU);
          END;
        ELSE 
          StatementSeq(default,lab);
        END;
        CodeLabel(exitLabel);
        FreeTemp(selTmp);
      END;
    END EncodeCase;

   (* ============================================================ *)

    PROCEDURE EncodeFor(stat : StatDesc);
      TYPE TrickWord =
        	RECORD
                  CASE (**) : BOOLEAN OF
                  | TRUE  : int : INTEGER;
                  | FALSE : crd : CARDINAL;
                  END;
                END;

      VAR base, cvTyp : TypeDesc;
          preTst, hard, signed, posStp, cvUplev : BOOLEAN;

          cvHigh, cvLow,
          initHigh, finalHigh,
          initLow, finalLow : TrickWord;

          absStep : INTEGER;
          cvObj   : Object;
          fiIndex : CARDINAL;
          iniExp, finExp : TempIndex;

      PROCEDURE highest(exp : ExprDesc) : CARDINAL;
        (*
         *  this procedure return the highest possible
         *  value of the expression, cast to cardinal
         *)
      BEGIN
        IF exp^.exprClass <> literalNode THEN
          RETURN MaxOfOrdType(exp^.exprType);
        ELSIF Compatible(exp^.exprType,charPtr) THEN
          RETURN ORD(exp^.conValue.charValue);
        ELSE RETURN exp^.conValue.fixValue;
        END;
      END highest;

      PROCEDURE lowest(exp : ExprDesc) : CARDINAL;
        (*
         *  this procedure return the lowest possible
         *  value of the expression, cast to cardinal
         *)
      BEGIN
        IF exp^.exprClass <> literalNode THEN
          RETURN MinOfOrdType(exp^.exprType);
        ELSIF Compatible(exp^.exprType,charPtr) THEN
          RETURN ORD(exp^.conValue.charValue);
        ELSE RETURN exp^.conValue.fixValue;
        END;
      END lowest;

      VAR eLab : LabelType;	(* loop entry label *)
          once : BOOLEAN;

    BEGIN
      AllocLabel(lLab);
      AllocLabel(xLab);
      AllocLabel(eLab);
      WITH stat^ DO
        posStp := stepSize > 0;
        hard   := (initial^.exprClass <> literalNode) OR
        		(final^.exprClass <> literalNode);
        (*
         * ALL limits and test are based on "int" or "unsigned"
         *)
        cvTyp := controlVariable^.varType;
        cvObj := baseObjOf(cvTyp);
        base  := baseTypeOf(cvTyp);

        cvUplev := uplevAcc IN controlVariable^.varUseSet;
        IF  (base^.tyClass = chars) OR
            (base^.tyClass = enums) THEN
          signed := FALSE;
        ELSE signed := IsSignedType(base);
        END;
        (*
         *  the need for the two kind of final test
         *  is evaluated here, for the four cases
         *)
        finalHigh.crd := highest(final);
        finalLow.crd  := lowest(final);
        initHigh.crd  := highest(initial);
        initLow.crd   := lowest(initial);
        cvHigh.crd    := MaxOfOrdType(cvTyp);
        cvLow.crd     := MinOfOrdType(cvTyp);

        (*
         *   The following test is needed in case the init
         *   expression is not same signed/unsigned mode
         *   as the control variable. In this case the values
         *   are adjusted so as to reflect the checked limits.
         *
         *   After this the init* values reflect the smallest
         *   range-checked overlap of initial with cv rep-type.
         *)
        IF signed THEN (* cv is signed *)
          IF initLow.int > initHigh.int THEN
            (* a card expr has wrapped around *)
            initHigh.int := cvHigh.int;
          END;
        ELSIF initLow.crd > initHigh.crd THEN
          (* an int expr has wrapped around *)
          initLow.crd := cvLow.crd;
          IF initHigh.crd > cvHigh.crd THEN
            initHigh.crd := cvHigh.crd;
          END;
        END;

       IF posStp THEN
          IF signed THEN
            IF initLow.int > finalHigh.int THEN RETURN END; (* no loop *)
            preTst := initHigh.int > finalLow.int;
          ELSE
            IF initLow.crd > finalHigh.crd THEN RETURN END; (* no loop *)
            preTst := initHigh.crd > finalLow.crd;
          END;
        ELSE (* neg step *)
          IF signed THEN
            IF initHigh.int < finalLow.int THEN RETURN END; (* no loop *)
            preTst := initLow.int < finalHigh.int;
          ELSE (* unsigned, negative step *)
            IF initHigh.crd < finalLow.crd THEN RETURN END; (* no loop *)
            preTst := initLow.crd < finalHigh.crd;
          END;
        END; (* neg step *)
        (*
         *  All necessary attributes are now evaluated,
         *  generation of code starts below.
         *
         *  if the control variable is uplevel accessed, the 
         *  value must be saved to memory prior to the body
         *  so that any accesses from called procs will find
         *  the current value rather than the original
         *
         *
         *  Code format is --		(with pretest)
         *
         *   +--------- <preTst>
         *   |		<assign>
         *   |		branch  eLab ---+
         *   |				|
         *   |   +--> lLab:		|
         *   |   |	<modify>	|
         *   |   |    eLab:	<-------+
         *   |   |	<loop body>
         *   |   +-----	<brkTst>
         *   +------> xLab:
         *
         *  Code format is --	     (without pretest)
         *
         *		<assign>
         *		branch  eLab ---+
         *				|
         *       +--> lLab:		|
         *       |	<modify>	|
         *       |    eLab:	<-------+
         *       |	<loop body>
         *       +-----	<brkTst>
         *)
        absStep := ABS(stepSize);
       (*
        *  If either limit is a variable, we must 
        *  compute the number of iterations at runtime
        *  by the following code, else use the consts.
        *)
        IF hard THEN 
          iniExp := newTemp(base);
          finExp := newTemp(base);
          IF posStp THEN 
            PushExprValue(final);
            MakeTemp(finExp);
          END;
          PushExprValue(initial);
          IF rangeTests IN initial^.testFlags THEN
            Test(cvTyp,initial^.exprType); (* dst,src *)
          END;
          MakeTemp(iniExp);
          IF NOT posStp THEN 
            PushExprValue(final);
            MakeTemp(finExp);
          END;
          Sub(none);
          IF absStep > 1 THEN
            PushCrd(absStep);
            DivU();		(* unsigned divide *)
          END;
         (*
          *  Top of the abstract stack is now the 
          *  required number of loop iterations
          *)
          StoreVal(countDownVar, directLocl, word);
        END; (* "if hard" *)
       (* $T- *)
        once := NOT hard AND 
        		(ABS(finalHigh.int - initHigh.int) DIV absStep = 0);
       (* $T= *)
       (*
        *  Now do the pretest if required ...
        *  Note that if not hard, then no test.
        *)
        IF preTst AND hard THEN
          PushTemp(iniExp);
          PushTemp(finExp);
          IF posStp THEN
            (* test if initial > final, and so on*)
            IF signed THEN IntRelopTrue(greaterNode, xLab);
            ELSE CardRelopTrue(greaterNode, xLab);
            END;
          ELSIF signed THEN IntRelopTrue(lessNode, xLab);
          ELSE CardRelopTrue(lessNode, xLab);
          END;
         (*
          *  jump over loop 
          *)
        END; (* if preTst *)
       (*
        *  Now assign the starting value ...
        *)
        IF hard THEN PushTemp(iniExp) ELSE PushInt(initHigh.int) END;
        StoreVal(controlVariable, directLocl, cvObj);

        IF once THEN StatementSeq(forBody,lab); RETURN END;

        Branch(eLab);
       (*
        *  Now start the loop body ...
        *)
        CommentLabel(lLab, "FOR loop label"); 
       (*
        *  now adjust the control variable (if no range check)
        *)
        PushVal(controlVariable, directLocl, cvObj);

        PushInt(stepSize);
        Add(none);
        IF rangeTests IN final^.testFlags THEN
          Test(cvTyp, final^.exprType);
        END;
        StoreVal(controlVariable, directLocl, cvObj);
       (*
        *  Now adjust the iteration count.
        *)
        IF hard THEN (* decrement *)
          PushVal(countDownVar, directLocl, word);
          PushCrd(1);
          Sub(none);
          StoreVal(countDownVar, directLocl, word);
        END;
       (*
        *  now emit the loop body
        *)
        CodeLabel(eLab);
        StatementSeq(forBody, lab);
       (*
        *  now do the termination test ...
        *)
        IF hard THEN (* decrement *)
          PushVal(countDownVar, directLocl, word);
          BranchNEZ(lLab);
        ELSE
          PushVal(controlVariable, directLocl, cvObj);
         (* $T- *) (* $R- *)
          PushInt(finalHigh.int - stepSize);
          IF posStp THEN
            IF signed THEN 
              IntRelopFalse(greaterNode, lLab);
            ELSE 
              CardRelopFalse(greaterNode, lLab);
            END;
          ELSE
            IF signed THEN 
              IntRelopFalse(lessNode, lLab);
            ELSE 
              CardRelopFalse(lessNode, lLab);
            END;
          END;
         (* $T= *) (* $R= *)
        END;
        WriteComment("end FOR loop");
        IF preTst THEN CodeLabel(xLab) END;
        IF hard THEN
          FreeTemp(iniExp);
          FreeTemp(finExp);
        END;
      END; (* with *)
    END EncodeFor;

   (* ============================================================ *)

    PROCEDURE EncodeIf(stat : StatDesc);
      VAR xLab : LabelType; (* the exit label *)
          tLab : LabelType; (* the true label *)
          fLab : LabelType; (* the false label *)
          cursor : ElemPtr;
          branch : IfDesc;
    BEGIN
      AllocLabel(xLab);
      InitCursor(stat^.branches,cursor);
      WHILE NOT NextIsLast(cursor) DO
        GetNext(cursor,branch);
        AllocLabel(fLab);
        WITH branch^ DO
          Assert(condition <> NIL);
          FallTrue(condition, fLab);
          StatementSeq(statSeq, lab);
        END;
        Branch(xLab);
        CodeLabel(fLab);
      END;
      GetNext(cursor,branch);
      WITH branch^ DO
        IF condition <> NIL THEN (* ==> no elsepart *)
          FallTrue(condition, xLab);
        END;
        StatementSeq(statSeq, lab);
      END;
      CodeLabel(xLab);
    END EncodeIf;

   (* ============================================================ *)

    PROCEDURE WriteProcCall(stat : StatDesc);

      VAR seq      : Sequence;

      PROCEDURE CallStandardProc(id : StandardProcs);
        VAR curs : ElemPtr;
            par1 : ExprDesc;
            par2 : ExprDesc;
            next : ExprDesc;
            pSiz : CARDINAL;
            xLab : LabelType;
            sign : BOOLEAN;
            test : BOOLEAN;
            sngl : BOOLEAN;   (* append single elem *)
            entr : BOOLEAN;   (* entire designator  *)
            mode : ModeEnum;
            pType : TypeDesc; (* type desc of par1  *)
            class : TyNodeClass;
            objct : Object;
            dVar  : IdDesc;
            dMod  : AccessMode;
            pName : CatEnum;
            uTmp,vTmp,wTmp,xTmp : TempIndex;
      BEGIN
        InitCursor(seq,curs);
        IF NOT Ended(curs) THEN
          GetNext(curs,par1);
          pType := par1^.exprType;
          IF NOT Ended(curs) THEN
            GetNext(curs,par2);
          ELSE par2 := NIL;
          END;
        END;
        CASE id OF
        | newP, disP : (* only the Vector types occur here *)
           (*
            * layout of stringtype is ...
            *
            *    ref	     obj	   blob
            *   [===] ---> +-----+
            *              |    -+-----> +-----+
            *              | hi  |       |     | num * size
            *              | num |       |     |
            *              +-----+       v     v
            *)
            IF par2 = NIL THEN RETURN END;
            IF id = newP THEN (* new(var,num,alloc) *)
             (*
              *    Construct object ...
              *)
              uTmp := newTemp(pType);
              PushCrd(pType^.targetType^.size);
              PushExprValue(par2);            (* number of elements *)
              CallVectorCtor;
              StoreTemp(uTmp);
             (*
              *    Store in destination.
              *)
              Designator(par1^.name, FALSE);
              PushTemp(uTmp);
              StoreInd(word);
              FreeTemp(uTmp);
            ELSE
             (*
              *    Get object reference
              *)
              DerefDesig(par1^.name, word);
              CallVectorDtor;
              Designator(par1^.name, FALSE);
              PushZero(word);
              StoreInd(word);                 (* set variable NIL  *)
            END;
        | resetP :
            PushExprValue(par1);
            IF rangeTests IN par2^.testFlags THEN 
              uTmp := newTemp(PointerTo(ints));
              Duplicate; 			(* -|,&vc,&vc		*)
              GetVectorHigh;            	(* -|,&vc,hi		*)
              StoreTemp(uTmp);    		(* -|,&vc,		*)
              PushExprValue(par2);		(* -|,&vc,new       	*)
              VariableCheck(uTmp,-1);
              FreeTemp(uTmp);
            ELSE
              PushExprValue(par2);		(* -|,&vc,new		*)
            END;
            PutVectorHigh;              	(* -|			*)
        | appendP :
            sngl  := stat^.appendClass = 2;
            wTmp  := invalid;
            vTmp  := invalid;
           (*
            *  The field stat^.appendClass has the following meanings:
            *   0:  a vector to vector append, mutating the first arg.
            *   1:  an array to vector append, mutating the first arg.
            *   2:  a simple, single element append to the first arg.
            *)
            AllocLabel(xLab);
            uTmp := newTemp(pType);             (* object reference     *)
            xTmp := newTemp(PointerTo(ints));   (* new high int value   *)
            IF NOT sngl THEN wTmp := newTemp(PointerTo(ints)) END;

            PushExprValue(par1);
            MakeTemp(uTmp);
            GetVectorHigh();                    (* ... hi               *)
            pType := par1^.exprType^.targetType;
           (*
            *  Get the length increment for each case and
            *  add it to high to get new high.
            *
            *  uTmp : reference to the target vector
            *  vTmp : reference to the source vector
            *  wTmp : increment in high value
            *  xTmp : new high value, after append
            *)
            IF stat^.appendClass = 0 THEN	(* stringT appendee     *)
              vTmp := newTemp(PointerTo(adrs)); (* src2 obj reference   *)
              PushExprValue(par2);              (* ... hi,&p2           *)
              MakeTemp(vTmp);                   (* ... hi,&p2           *)
              GetVectorHigh;                    (* ... hi,hi2           *)
              PushInt(1);                       (* ... hi,hi2,1         *)
              Add(none);                        (* ... hi,ln2           *)
              MakeTemp(wTmp); 
            ELSIF stat^.appendClass = 1 THEN	(* arrays *)
              IF par2^.exprType^.isDynamic THEN
                Assert(par2^.exprClass = desigNode);
                PushOpenCount(par2);            (* ... hi,ln2           *)
              ELSE			        (* fixed array append   *)
               	PushCrd(IndexCardinality(par2^.exprType));
              END;
              MakeTemp(wTmp); 
            ELSE
              PushCrd(1);                       (* ... hi, 1            *)
            END;
            Add(none);                          (* ... new hi = 'nhi'   *)
            MakeTemp(xTmp);
           (*
            *  Check if this equals the limit ...
            *)
            PushTemp(uTmp);                     (* ... nhi,&p1          *)
            GetVectorLimit();                   (* ... nhi,lim          *)
            IntRelopTrue(lessNode, xLab);       (* ... <empty>          *)
           (*
            *  If the limit is broken, then call
            *  str.__Expand(extraNum);
            *)
            PushTemp(uTmp);     (* the mutable vector *)
            PushTemp(xTmp);     (* the new high value *)
            CallVectorExpand;
            CodeLabel(xLab);
           (*
            *  Now append the elements ...
            *)
            PushTemp(uTmp);                     (* ... &p1              *)
            GetVectorBlob();                    (* ... &dt              *)
            IF sngl THEN
              PushTemp(xTmp);                   (* ... &dt,nhi          *)
            ELSE
              PushTemp(uTmp);                   (* ... &dt,&p1          *)
              GetVectorHigh();                  (* ... &dt,ohi          *)
              PushInt(1);                       (* ... &dt,ohi,1        *)
              Add(none);                        (* ... &dt,ln1          *)
            END;
            IF pType^.size > 1 THEN
              PushInt(pType^.size);
              Mul(none);
            END;
            Add(none);                          (* adr. of insert pos'n *)
           (*
            *  uTmp : reference to the target vector
            *  vTmp : reference to the source vector
            *  wTmp : increment of high value
            *  xTmp : new high value, after append
            *)
            IF stat^.appendClass = 0 THEN
              PushTemp(vTmp);                   (* ... &ip,&p2          *)
              GetVectorBlob;                    (* ... &ip,&dt2         *)
              PushTemp(wTmp);                   (* ... &ip,&dt2,&ln2    *)
              IF pType^.size > 1 THEN
                PushInt(pType^.size);
                Mul(none);
              END;
              CopyBlock(pType^.alignMask);      (* ... <empty>          *)
            ELSIF stat^.appendClass = 1 THEN
              vTmp := newTemp(par2^.exprType);
              MkObjAndPushAdr(par2, vTmp);      (* ... &ip,&arr         *)
              PushTemp(wTmp);                   (* ... &ip,&arr,ln2     *)
              IF pType^.size > 1 THEN
                PushInt(pType^.size);
                Mul(none);
              END;
              CopyBlock(pType^.alignMask);      (* ... <empty>          *)
            ELSIF needsCopy(par2^.exprType^.tyClass, par2^.exprType^.size) THEN
              vTmp := newTemp(par2^.exprType);
              MkObjAndPushAdr(par2, vTmp);      (* ... &ip,&elem        *)
              PushCrd(par1^.exprType^.targetType^.size); 
              CopyBlock(pType^.alignMask);      (* ... <empty>          *)
            ELSE
              PushExprValue(par2);              (* ... &ip,elem         *)
              StoreInd(baseObjOf(pType));       (* ... <empty>          *)
            END;
            PushTemp(uTmp);                     (* ... &p1              *)
            PushTemp(xTmp);                     (* ... &p1,newHigh      *)
            PutVectorHigh;                      (* ... <empty>          *)
            (* 
             *  Note: the in-scope allocate and deallocate 
             *  id-descriptors are present here as par-3 and par-4
             *)
            FreeTemp(uTmp);
            FreeTemp(xTmp);
            IF NOT sngl THEN FreeTemp(wTmp) END;
            FreeTemp(vTmp);
        | concatP :
            PushExprValue(par1);
            IF  (par2^.exprType^.tyClass = stringTs) THEN
              PushExprValue(par2);
              pName := stCat;
            ELSIF par2^.exprType^.tyClass = SS THEN
              PushCon(par2^.rtOffset);
              PushCrd(par2^.conValue.strHigh + 1);
              pName := ssCat;
            ELSIF par2^.exprType^.tyClass = arrays THEN
              uTmp := newTemp(par2^.exprType);
              MkObjAndPushAdr(par2, uTmp);
              IF par2^.exprType^.isDynamic THEN
        	Assert(par2^.exprClass = desigNode);
        	PushOpenCount(par2);
              ELSE
        	PushCrd(IndexCardinality(par2^.exprType));
              END;
              pName := ssCat;
              FreeTemp(uTmp);
            ELSE (* S1, chars, subranges of char *)
              PushExprValue(par2);
              pName := chCat;
            END;
            CallVectorConcat(pName);
            (* 
             *  Note: the in-scope allocate and deallocate 
             *  id-descriptors are present here as par-3 and par-4
             *)
        | haltP : (* are these macros, syscalls or libc calls ? *)
            PushCrd(0);
            MkTrap(exitTrp);
        | abortP :
            MkTrap(abortTrp);
        | incP, decP :
            sign := IsSignedType(pType);
            test := ovfloTests IN par1^.testFlags;
            mode := addMode[sign, test];
            class := pType^.tyClass;
            objct := baseObjOf(pType);

            dMod := AccessModeOf(par1^.name);
            entr := isSimpleDes(par1^.name, dMod);
            IF entr THEN
              PushVal(par1^.name.variable, dMod, objct);
            ELSE
              Designator(par1^.name, FALSE);
              Duplicate;
              LoadInd(objct);
            END;
            PushExprValue(par2);
            IF id = incP THEN Add(mode) ELSE Sub(mode) END;
            IF rangeTests IN par1^.testFlags THEN 
              IF sign THEN Test(pType, PointerTo(ints));
              ELSE Test(pType, PointerTo(cards));  (* dst,src *)
              END;
            END;
            IF entr THEN
              StoreVal(par1^.name.variable, dMod, objct);
            ELSE
              StoreInd(objct);
            END;
        | exclP, inclP :
            IF pType^.size > bytesInWord THEN
              Designator(par1^.name, FALSE);
              PushExprValue(par2);
              IF rangeTests IN par2^.testFlags THEN
        	Test(pType^.baseType, par2^.exprType);
              END;
              BigSetIncl(id = inclP);
            ELSE
              dMod := AccessModeOf(par1^.name);
              entr := isSimpleDes(par1^.name, dMod);
              IF entr THEN
                PushVal(par1^.name.variable, dMod, word);
              ELSE
                Designator(par1^.name, FALSE);
                Duplicate;
                LoadInd(word);
              END;
              PushCrd(1);
              PushExprValue(par2);
              IF rangeTests IN par2^.testFlags THEN
        	Test(pType^.baseType, par2^.exprType);
              END;
              LShift;
              IF id = exclP THEN NegBits; BitAND ELSE BitOR END;
              IF entr THEN
                StoreVal(par1^.name.variable, dMod, word);
              ELSE
                StoreInd(word);
              END;
            END;
        | addAdrP, subAdrP : Assert(FALSE,"bad incAdr");
        | shiftP, rotateP :
            Assert(par1^.exprClass = desigNode);
            dMod := AccessModeOf(par1^.name);
            entr := isSimpleDes(par1^.name, dMod);
            IF entr THEN
              PushVal(par1^.name.variable, dMod, word);
            ELSE
              Designator(par1^.name, FALSE);
              Duplicate;
              LoadInd(word);
            END;
            IF id = shiftP THEN
              IF par2^.exprClass # literalNode THEN
                PushExprValue(par2);
                Shift;
              ELSIF par2^.conValue.intValue > 0 THEN
                PushInt(par2^.conValue.intValue);
                LShift;
              ELSIF par2^.conValue.intValue < 0 THEN
                PushInt(-par2^.conValue.intValue);
                RShift;
             (* ELSE stack value is correct already *)
              END;
            ELSE
             (*
              *  Could fold rhs literals here ...
              *)
              uTmp := newTemp(par1^.exprType);    (* lhs value   *)
              MakeTemp(uTmp);
              IF par2^.exprClass # literalNode THEN
                vTmp := newTemp(par1^.exprType);  (* rhs MOD(32) *)
                PushExprValue(par2);
                PushCrd(bitsInWord-1);
                BitAND;
                MakeTemp(vTmp);
                LShift;
                PushTemp(uTmp);
                PushCrd(bitsInWord);
                PushTemp(vTmp);
                Sub(none);
                FreeTemp(vTmp);
              ELSE
                PushCrd(par2^.conValue.fixValue MOD 32);
                LShift;
                PushTemp(uTmp);
                PushCrd(32 - par2^.conValue.fixValue MOD 32);
              END;
              LRShift;
              BitAND;
              FreeTemp(uTmp);
            END;
            IF entr THEN
              StoreVal(par1^.name.variable, dMod, word);
            ELSE
              StoreInd(word);
            END;
        | exitP :
            PushExprValue(par1);
            MkTrap(exitTrp);
        | assertP, preconP :
            IF NOT (assertOff IN modState) AND
        	((par1^.exprClass <> literalNode) OR
        	 (par1^.conValue.fixValue = ORD(FALSE))) THEN
              AllocLabel(xLab);
              FallFalse(par1, xLab);
              IF par2 = NIL THEN
                PushModName; 
                PushCrd(stmnt^.sourceLoc.line);
              ELSIF par2^.actualX^.exprType^.tyClass = SS THEN
                PushCon(par2^.actualX^.rtOffset);
                PushCrd(0);
              ELSE
                uTmp := newTemp(par2^.actualX^.exprType);
                MkObjAndPushAdr(par2^.actualX, uTmp);
                PushCrd(0);
                FreeTemp(uTmp);
              END;
              MkTrap(assTrp);
              CodeLabel(xLab);
            END;
        END;
      END CallStandardProc;

      VAR typ  : TypeDesc;
          pNum : CARDINAL;
          pVar : BOOLEAN;
          list : TempList;

    BEGIN
      WITH stat^.designator DO
        (*
         *  first must check here for standard procs
         *)
        seq := stat^.actualParams;
        IF  (variable^.idClass = stProc) OR
            (* only for backward compat for rotate and shift *)
            (variable^.idClass = stFunc) THEN
          CallStandardProc(variable^.procVal);
        ELSE (* now the actual call *)
          pVar := (variable^.idClass = varNode);
         (*
          *  for the CLR version, for calli, the designator
          *  is pushed last, after the parameters
          *)
          IF pVar THEN
            typ := typeOfDes(stat^.designator);
            (* ... and there is no static link *)
          ELSE 
            typ := variable^.procType;
            PushStaticLink(variable);
          END;
          list := NIL;
          DoParams(typ, seq, pNum, list);
          IF pVar THEN
            DerefDesig(stat^.designator, word);
            CallTos(typ, pNum, 0, FALSE);
          ELSE 
            CallMth(variable, pNum, 0);
          END;
          FreeGroup(list);  (* MUST COME AFTER CALL *)
        END;
      END;
    END WriteProcCall;

   (* ----------------------------------------------------------- *)

    PROCEDURE BigSetAssign(exp : ExprDesc);
      VAR size : CARDINAL;
          dTmp : TempIndex;
      (* pre  : destination address is top of stack *)
      (* post : stack is popped by one ...	    *)
    BEGIN
      size := exp^.exprType^.size;
      dTmp := newTemp(exp^.exprType);
      MkSetAndPushAdr(exp, size DIV bytesInWord, dTmp);
      PushCrd(size);
      CopyBlock(alignMap[bytesInWord]);
      FreeTemp(dTmp);
    END BigSetAssign;

   (* ----------------------------------------------------------- *)

    PROCEDURE RetBoolExpr(expr : ExprDesc);
    (* Return a Boolean expression value, emitting jumping code *)
      PROCEDURE RetHelper(fOrT : BOOLEAN; expr : ExprDesc);
        VAR newL : LabelType;
      BEGIN
        CASE expr^.exprClass OF
        | notNode :
            RetHelper(NOT fOrT, expr^.notOp);
        | orNode  : 
            AllocLabel(newL);
            FallTrue(expr^.leftOp, newL);
            PushCrd(ORD(fOrT)); 
            Return;
            CodeLabel(newL);
            RetHelper(fOrT, expr^.rightOp);
        | andNode : 
            AllocLabel(newL);
            FallFalse(expr^.leftOp, newL);
            PushCrd(ORD(NOT fOrT)); 
            Return;
            CodeLabel(newL);
            RetHelper(fOrT, expr^.rightOp);
        ELSE
            PushExprValue(expr); (* bound to be Boolean *)
            IF NOT fOrT THEN NegBool END;
        END;
      END RetHelper;
    BEGIN
      RetHelper(TRUE, expr);
    END RetBoolExpr;

   (* ----------------------------------------------------------- *)

    VAR dTmp : TempIndex;
        xTyp : TypeDesc;
        smpl : BOOLEAN;
        mode : AccessMode;

  BEGIN (* body of StatementSeq *)
    InitCursor(seq,cursor);
    WHILE NOT Ended(cursor) DO
      GetNext(cursor,stmnt);
      WITH stmnt^ DO
        IF statClass <> emptyNode THEN
          IF debugOn THEN LineNum(sourceLoc.line) END;
        END;
       (* ----------------------------------- *)
        CASE statClass OF
        | compoundNode : StatementSeq(inlineBody,lab);
        | emptyNode    : (* nothing *)
        | forNode      : EncodeFor(stmnt);
        | exitNode     : Branch(lab);
        | procCallNode : WriteProcCall(stmnt);
        | ifNode       : EncodeIf(stmnt);
        | caseNode     : EncodeCase(stmnt);
       (* ----------------------------------- *)
        | assignNode :  
            xTyp  := expression^.exprType;
            class := xTyp^.tyClass;
            mode  := AccessModeOf(designator);
            smpl  := isSimpleDes(designator, mode);

            IF class = sets THEN
              IF xTyp^.size <> bytesInWord THEN (* big set *)
                Designator(designator, FALSE);
                BigSetAssign(expression);	(* pops the desig *)
              ELSIF smpl THEN
                PushExprValue(expression);
                StoreVal(designator.variable, mode, word);
              ELSE
                Designator(designator, FALSE);
                PushExprValue(expression);
(* -- *)        StoreInd(word);
              END;
            ELSIF class = RR THEN
              object := table[desigType^.tyClass];
              IF smpl THEN
                PushRR(expression, object);
                StoreVal(designator.variable, mode, object);
              ELSE
                Designator(designator, FALSE);
                PushRR(expression, object);
(* -- *)        StoreInd(object);
              END;
            ELSIF NOT (class IN specials) THEN  (* sets elsewhere *)
              object := baseObjOf(desigType);
              IF NOT smpl THEN Designator(designator, FALSE) END;
              IF object = hugeInt THEN
                PushLongValue(expression);
              ELSE
                PushExprValue(expression);
                IF rangeTests IN expression^.testFlags THEN 
                  Test(desigType, xTyp); (* dst,src *)
                END;
              END;
              IF smpl THEN 
                StoreVal(designator.variable, mode, object);
              ELSE
(* -- *)        StoreInd(object);
              END;
            ELSIF class = SS THEN
              length := desigType^.size;
              Designator(designator, FALSE);
              PushExprAddress(expression);
              IF length > expression^.conValue.strHigh THEN
                PushCrd(expression^.conValue.strHigh + 1);
              ELSE PushCrd(length);
              END;
              CopyBlock(alignMap[1]);		(* pops all three *)
            ELSE (* arrays and records *)
              align := xTyp^.alignMask;
              Designator(designator, FALSE);
              dTmp := newTemp(xTyp);
              MkObjAndPushAdr(expression, dTmp);
              PushCrd(xTyp^.size);
              CopyBlock(align);			(* pops the desig *)
              FreeTemp(dTmp);
            END;
       (* ----------------------------------- *)
        | loopNode     :
            AllocLabel(lLab);
            AllocLabel(xLab);
            CommentLabel(lLab, "LOOP loop label");
            StatementSeq(loopBody, xLab);
            Branch(lLab);		    (* loop here *)
            WriteComment("end LOOP loop");
            CodeLabel(xLab);		    (* exit here *)
       (* ----------------------------------- *)
        | returnNode   :
            IF returnResult <> NIL THEN
              xTyp  := returnResult^.exprType;
              class := xTyp^.tyClass;
              IF needsCopy(class, destTypeDesc^.size) THEN
               (*
                *  result could be in local ==> copy to dst
        	*)
                dTmp := newTemp(xTyp);
                MkObjAndPushAdr(returnResult, dTmp);
                LoadObj(xTyp);
                FreeTemp(dTmp);
              ELSIF class = RR THEN
        	PushRR(returnResult, table[destTypeDesc^.tyClass]);
              ELSIF class = bools THEN
        	RetBoolExpr(returnResult);
              ELSE (* NOT special + small sets *)
                PushExprValue(returnResult);
                IF rangeTests IN returnResult^.testFlags THEN 
        	  Test(destTypeDesc, xTyp); (* dst,src *)
                END;
              END;
            END;
            IF returnLab = 0 THEN Return() ELSE Branch(returnLab) END;
       (* ----------------------------------- *)
        | whileNode    :  
            AllocLabel(lLab);
            AllocLabel(xLab);
            FallTrue(condition, xLab);
            (*
             * loop header, invariant code goes here
             *)
            CommentLabel(lLab, "WHILE loop label"); 

            StatementSeq(wrBody,lab);
            FallFalse(condition, lLab);
            WriteComment("end WHILE loop");
            CodeLabel(xLab);
       (* ----------------------------------- *)
        | repeatNode   :   
            AllocLabel(lLab);
            (*
             * loop header, invariant code goes here
             *)
            CommentLabel(lLab, "REPEAT loop label"); 
            StatementSeq(wrBody,lab);
            FallTrue(condition, lLab);
            WriteComment("end REPEAT loop");
       (* ----------------------------------- *)
        | withNode     :    
            WITH withInfo^ DO
              dTmp := invalid;
             (*
              *  In a withNode, M2Traveral copies desig.variable
              *  to the "dummy" field if :
              *   -  desig is an entire variable, AND
              *   -  desig is a static field
              *  Otherwise dummy is an anon identifier which
              *  will hold a pointer to the selected record.
              *)
              IF desig.variable <> dummy THEN
                dTmp := newTemp(PointerTo(adrs));
        	Designator(desig, FALSE);
               (*
        	*  this places the address of the designator
        	*  on the top of stack. It is always a mem-temp
        	*)
                StoreTemp(dTmp);
                dummy^.varOffset := dTmp-1;
              END;
              StatementSeq(withBody, lab);
              FreeTemp(dTmp);
            END;
       (* ----------------------------------- *)
        END; (* of case *)
      END; (* with stmnt^ *)
    END;
  END StatementSeq;


  PROCEDURE EmitBlock(idd : IdDesc);
    VAR index     : INTEGER;
  BEGIN
    WITH idd^ DO
      inExcept := FALSE;
      GenerateEntry(idd);
     (*
      * emit the dynamic nested module bodies
      *)
      IF idd^.idClass  <> modNode THEN EmitMods(body^.nestBlks) END;
     (*
      * emit the code body
      *)
      returnLab := 0;	(* RETURN = exit *)
      StatementSeq(body^.statements,0);
      IF debugOn THEN LineNum(body^.endIdLine) END;
      IF  (idClass IN procSet) AND 
          (procType^.tyClass = funcTypes) THEN
        MkTrap(funTrp);
      ELSE
        Return();
      END;
      GenerateExit(idd);
    END;
  END EmitBlock;

 (* =========================================================== *
  * This procedure recurses over the "nestBlks" strings. This
  * version emits procedures separately, in post-order, merrily
  * recursing past modules, without emitting their code.
  * =========================================================== *)
  PROCEDURE EmitProcs(str : IdString);
    VAR idx : INTEGER;
        idd : IdDesc;
  BEGIN
    FOR idx := 0 TO HIGH(str) DO
      idd := str[idx];
      WITH idd^ DO
       (*
        *   It is necessary to define the XSR's before
        *   emitting nested procs, since these *will* 
        *   access uplevel data, and need to know offsets
        *   in the eXplicit Stack-allocated Record.
        *)
        IF hasXSR(idd) THEN DefineXSR(idd) END;
       (*
        *   Now do the recursion
        *)
        EmitProcs(body^.nestBlks); (* recurse down past modNodes *)
       (*
        *   Now emit code for this procedure
        *)
        IF idClass <> modNode THEN EmitBlock(idd) END;
      END;
    END;
  END EmitProcs;

 (* =========================================================== *
  * Emit the static features of this module body.
  * =========================================================== *)
  PROCEDURE EmitStaticFeatures(mid : IdDesc);
    VAR idd : IdDesc;
        idx : INTEGER;
        jdx : CARDINAL;
        str : IdString;
        hsh : HashBucketType;
        main : BOOLEAN;
  BEGIN
    jdx := 0;
    hsh := mid^.name;
    str := mid^.body^.nestBlks;
    NamespaceBegin(hsh, mid);
    ClassBegin(hsh);
   (*
    *  If this is the outer module, then
    *  emit the constant pool lit chain.
    *)
    main := mid = thisCompileUnit;
    IF main THEN EmitLitChain() END;
   (*
    *  Now emit the static fields and static methods.
    *  First: static fields 
    *)
    EmitMyVars(mid, mid^.scope);
   (*
    *  Next: static methods 
    *)
    FOR idx := 0 TO HIGH(str) DO
      idd := str[idx];
      WITH idd^ DO
        IF idClass <> modNode THEN
          IF hasXSR(idd) THEN DefineXSR(idd) END;
         (*
          *  Emit all procedures nested within idd
          *  including those nested within dynamic
          *  modules declared local to a procedure.
          *)
          EmitProcs(idd^.body^.nestBlks);  
         (*
          *  Now emit the body of procedure idd.
          *)
          EmitBlock(idd);
        END;
      END;
    END;
   (* 
    *  Emit the initialization or body code
    *)
    EmitBlock(mid);
    IF main AND (progMod IN modState) THEN EmitWrapper() END;
    ClassEnd(hsh);
   (*
    *  Now emit any nested modules.
    *)
    FOR idx := 0 TO HIGH(str) DO
      idd := str[idx];
      WITH idd^ DO
        IF idClass = modNode THEN
          EmitStaticFeatures(idd);  
        END;
      END;
    END;
   (*
    *  If this is the outer module, then
    *  emit any queued up class declarations.
    *  AND any  queued-up pinvokeimpl methods ...
    *)
    IF main THEN 
      DoPInvokeImpls();
      EmitClassDefs();
      WriteWrappers();
    END;
    NamespaceEnd(hsh);
  END EmitStaticFeatures;

 (* =========================================================== *
  * This procedure recurses over the "nestBlks" strings. This
  * version emits modules, stopping when it gets to a procedure.
  * This version does: most nested first, left-to-right order.
  * =========================================================== *)
  PROCEDURE EmitMods(str : IdString);
    VAR idx : INTEGER;
        idd : IdDesc;
        exceptLab : LabelType;
  BEGIN
    FOR idx := 0 TO HIGH(str) DO
      idd := str[idx];
      WITH idd^ DO
        IF idClass = modNode THEN 
          EmitMods(body^.nestBlks);
          AllocLabel(returnLab);
         (*
          * emit the module body
          *)
          StatementSeq(body^.statements,0);
          CodeLabel(returnLab);	    (* RETURNs will jump forward to here *)
        END;
      END;
    END;
  END EmitMods;

(* ========================================================== *)

  PROCEDURE EmitOutput;
    VAR cursor : ElemPtr;
        idPtr  : IdDesc;
  BEGIN
    charPtr := PointerTo(chars);
    CreateObjFile(thisCompileUnit^.name);
   (*
    *  Emit the header comment
    *  and then the extern assemblies.
    *  Finally the const data, and namespace decl.
    *)
    DoObjHeader(thisCompileUnit^.name);
    (*
     *  Emit the dummy static class header,
     *  and then the static class data.
     *  Finally the module .cctor or main.
     *)
    EmitStaticFeatures(thisCompileUnit);
   (*
    *  Close off the namespace decl.
    *)
    DoObjEnd;
    CloseObjFile();
   (*
    *  What is the equivalent of the reference file
    *  computation in the CLR case? Watch this space!
    *  ... but in the meanwhile ...
    *)
    WriteRefFile(callSmbl());
  END EmitOutput;

END M2ClrCode.
