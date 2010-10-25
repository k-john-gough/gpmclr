(****************************************************************)
(*                                                              *)
(*              Modula-2 Compiler Source Module                 *)
(*                                                              *)
(*          Destination Marking for Set Expressions.            *)
(*                                                              *)
(*    (c) copyright 1988 Faculty of Information Technology.     *)
(*                                                              *)
(*      original module : kjg December 1988                     *)
(*      modifications   : 23-Nov-89 temporary now set of byte   *)
(*			  20-Feb-90 assign desigs now scanned   *)
(*			:  2-Nov-90 special dcode version (kjg) *)
(*			:  5-Nov-90 pre-alloc temporaries (kjg) *)
(*			: 19-Apr-91 temp bug in SetExpr         *)
(*			: 20-Apr-91 fix selector exprs in cases *)
(*			: 20-Jun-91 functions returning REAL	*)
(*			: 20-Sep-92 functions returning ARRAYS  *)
(*			: 04-Oct-92 other runtime constructors  *)
(*                                                              *)
(****************************************************************
$Log: m2settem.mod,v $
Revision 1.18  1997/01/16 05:02:46  gough
code for preconNode handling added

Revision 1.17  1996/11/27 02:52:11  lederman
add traversals over the except and finally statements

Revision 1.16  1996/11/14 04:48:59  gough
use the isStrIx flag to determine if a particular subscript expression
needs to be allocated a temporary location.

Revision 1.15  1996/08/07 23:44:08  gough
VARSTRS.CUT needs a temporary

Revision 1.14  1996/08/06 23:43:05  gough
skip errNode nodes in case statement (used for wrappers)

Revision 1.13  1996/07/30 00:01:49  gough
allocate temporaries for overloaded NEW and indexing into strings.

Revision 1.12  1995/09/15 07:57:00  gough
mark the transitions from jumping to value code, and alloc merge variable

Revision 1.11  1995/07/26 03:06:22  gough
fixed up fixed marshalling so that most stringent alignment is used
for the marshalling area.  Fixes bug in byteOpen copies.

# Revision 1.10  1995/03/17  02:12:26  gough
# allocate temporaries for castNode with large source expressions
#
# Revision 1.9  1995/03/14  01:47:51  gough
# Restructure ParamList, so as to process marshalling areas for value opens
#
# Revision 1.8  1995/03/02  08:50:31  gough
# traversal is modified to allow for, and correctly treat castNode exprs
#
# Revision 1.7  1994/10/10  05:14:25  gough
# allocating space in case of the sunStructs flag for the callee to copy
# value structures according to the SUN Microsystems convention for structs
#
# Revision 1.6  1994/09/05  02:42:53  gough
# all inNode's need a word temporary, for possible out of range check.
#
# Revision 1.5  1994/08/10  00:49:43  gough
# allocate temporary for case statement select expressions.
#
# Revision 1.4  1994/07/28  03:22:37  gough
# fix up treatment of selected constants in inNodes and setBinops
#
# Revision 1.3  1994/07/27  23:00:09  gough
#
# Revision 1.2  1994/07/01  05:36:33  lederman
# make alignments varaible on bytesInWord
#
# Revision 1.1  1994/04/07  05:19:38  lederman
# Initial revision
#
*****************************************************************
Revision 1.3  93/10/11  13:43:33  gough
The new for loop processing requires two temporary locations to be 
allocated if EITHER initial or final bounds are non-constant. Fixed here.
*****************************************************************)

IMPLEMENTATION MODULE M2SetTemporaries;

  IMPORT StdError;
  FROM SYSTEM IMPORT CAST;

  FROM M2Alphabets  IMPORT Flags, FlagSet;

  FROM GenSequenceSupport IMPORT
        Sequence, ElemPtr, Ended, IsEmpty,
        InitCursor, GetNext, GetFirst;

  FROM M2Designators IMPORT
        ExprDesc, ExprRec, ExprNodeClass,
        DesigRec, WithDesc, WithRec,
        SelectNodeClass, DStateType, SelectAttribute,
        InitDState, GetSelector, EmptySelList,
        fxVal, ActualParMode;

  FROM M2NodeDefs IMPORT
        StrucTree, StrucRec, current,
        IdDesc, IdRec, IdNodeClass, StandardProcs,
        TypeDesc, TypeRec, TyNodeClass;

  FROM M2StructureDefs IMPORT
        StatDesc, StatRec, StatNodeClass,
        RangeDesc, RangeRec,
        CaseStatDesc, CaseStatRec, CaseDesc, CaseRec,
        IfDesc, IfRec;

  FROM M2MachineConstants IMPORT wordSize, bytesInWord, sunStructs;
  FROM M2LitChain IMPORT FixLiteral;
  FROM ProgArgs IMPORT Assert;
  FROM M2NameHandler IMPORT anonBkt;
  FROM M2InOut IMPORT Position, DiagName;
  FROM M2NamGenerate IMPORT MakeNewCurrent;

  (*
   *	For this version (5-Nov-90) the following cases of 
   *    code-generator memory temporaries are treated ---
   *
   *  * with statement dummies  ( 2-Nov-90)
   *  * set constructors	( 5-Nov-90)
   *  * inNode nodes		( 5-Nov-90)
   *  * inclP and exclP		( 5-Nov-90)
   *  * for loop nodes		( 5-Nov-90)
   *
   *	For this version (20-Jun-91) the following is added
   *
   *  * functions returning REALs
   *
   *	For this version (20-Sep-92) the following is added
   *
   *  * functions returning ARRAYs and large SETs
   *
   *	For this version (04-Oct-92) the following is added
   *
   *  * runtime constructors for arrays and records
   *)

  (*==================================================*)
    MODULE TemporariesStack;
      IMPORT CAST;
      EXPORT Alloc, DeAlloc, InitCount, HiTide, Mark, Release;
      VAR count  : CARDINAL;
          hiTide : CARDINAL;

      PROCEDURE HiTide() : CARDINAL;
      BEGIN
        RETURN hiTide;
      END HiTide;

      PROCEDURE Mark() : CARDINAL;
      BEGIN
        RETURN count;
      END Mark;

      PROCEDURE Release(mark : CARDINAL);
      BEGIN
        count := mark;
      END Release;

      PROCEDURE InitCount();
      BEGIN
        count := 0; hiTide := 0;
      END InitCount;

      PROCEDURE Alloc(alignMask : CHAR;
		      byteCount : CARDINAL;
                      VAR index : CARDINAL);
      BEGIN
	count := CAST(CARDINAL,
			CAST(BITSET,(count + ORD(alignMask))) - 
			CAST(BITSET,ORD(alignMask))
		     );
        index := count;
        INC(count,byteCount);
        IF count > hiTide THEN hiTide := count END;
      END Alloc;

      PROCEDURE DeAlloc(byteCount : CARDINAL);
      BEGIN
        DEC(count,byteCount);
      END DeAlloc;

    END TemporariesStack;
  (*==================================================*)

    MODULE Marker;
      IMPORT StatDesc, StatRec, ExprDesc, ExprRec, Position;
      EXPORT MarkExp, MarkStat;

       (*
	*  the procedures of this module mark designators
	*  with the memory temporary offset to be used
	*  it reuses the sourceLoc.pos field 
	*)

	PROCEDURE MarkExp(exp : ExprDesc; offset : CARDINAL);
        BEGIN
	  exp^.sourceLoc.pos := offset;
	END MarkExp;

	PROCEDURE MarkStat(stat : StatDesc; offset : CARDINAL);
        BEGIN
	  stat^.sourceLoc.pos := offset;
	END MarkStat;

    END Marker;
  (*==================================================*)
  (*
   *  Note that this code is independent of the alignment used by
   *  any C system, or the underlying hardware, the system may 
   *  to do the alignment more strictly than the hardware requires,
   *  at the cost of a slight waste of space.
   *)

  TYPE   ExprClassSet = SET OF ExprNodeClass;
	 TyClassSet   = SET OF TyNodeClass;

  (*
   *  the following expr node classes are all the classes
   *  which need a destination location, and hence might
   *  need to be allocated a memory temporary 
   *)

  CONST  tmpCls = ExprClassSet{starNode, slashNode, plusNode,
                      minusNode, setDesigNode, funcDesigNode};

  CONST  cnOrFn = ExprClassSet{
			constructorNode, funcDesigNode, setDesigNode};

  CONST  allLts = ExprClassSet{
			literalNode, selConstNode};

  (* ------------------------------------------------- *)
  (* utility for general use : a set needs an explicit
     destination if set has size > bytes in word       *)

     PROCEDURE IsLargeSet(exp : ExprDesc) : BOOLEAN;
     BEGIN
       RETURN (exp^.exprType^.tyClass = sets) AND 
                (exp^.exprType^.size <> bytesInWord)
     END IsLargeSet;

     PROCEDURE SetWithTemp(exp : ExprDesc) : BOOLEAN;
     BEGIN
       RETURN (exp^.exprType^.tyClass = sets) AND 
                (exp^.exprType^.size <> bytesInWord) AND
		  (exp^.exprClass IN tmpCls);
     END SetWithTemp;

     PROCEDURE ExpWithTemp(exp : ExprDesc) : BOOLEAN;
     BEGIN
       RETURN (exp^.exprClass IN cnOrFn) AND
		((exp^.exprType^.tyClass = arrays) OR
		 (exp^.exprType^.tyClass = records));
     END ExpWithTemp;

  (* ------------------------------------------------- *)
  (* this procedure traverses actual parameter sequences
     allocating set temporaries as necessary           *)

    PROCEDURE ParamList(seq : Sequence);

      PROCEDURE DoParam(this : ExprDesc);
        VAR idx : CARDINAL;
      BEGIN
       (*
        *  avoid case of stFuncs with type-Id args.
        *  Note that later versions will fold sizeP and
        *  tsizeP, but the code is still needed for VAL()
        *)
        IF this^.exprType = NIL THEN
          (* Assert: param is type name, so skip *)
        ELSIF SetWithTemp(this) THEN
          Alloc(CHR(wordSize-1),this^.exprType^.size,idx);
          SetExpr(this,idx);
        ELSIF ExpWithTemp(this) THEN
          Alloc(this^.exprType^.alignMask,this^.exprType^.size,idx);
	  BigExpr(this,idx);
        ELSE
	  IF sunStructs AND
	     (this^.actualClass = valActual) AND
	     (this^.exprType^.tyClass = records) THEN
            Alloc(this^.exprType^.alignMask,this^.exprType^.size,idx);
	    MarkExp(this,idx);
	  END;
          OtherExpr(this);
        END;
      END DoParam;

      VAR tide : CARDINAL;
          curs : ElemPtr;
          parm : ExprDesc;
          indx : CARDINAL;
          aAgn,fAgn : CHAR;  (* actual and formal alignment *)

    BEGIN
      tide := Mark();
      InitCursor(seq,curs);
      WHILE NOT Ended(curs) DO
        GetNext(curs,parm);
	IF parm = NIL THEN
	ELSIF parm^.exprClass = openMarshallNode THEN
	  DoParam(parm^.actualX);
	ELSIF parm^.exprClass = fixedMarshallNode THEN
         (*
          *  Here, exprType is the formalType, which
          *  is the formal element type. In case of
          *  system types, align should come from actual
          *)
          fAgn := parm^.exprType^.alignMask;
          aAgn := parm^.actualX^.exprType^.alignMask;
          IF fAgn > aAgn THEN aAgn := fAgn END;
          Alloc(aAgn, parm^.mrshSiz, indx);
(*
StdError.WriteString("Alloc temp of size ");
StdError.WriteCard(parm^.mrshSiz,0);
StdError.WriteString(" gets ");
StdError.WriteCard(indx,0);
StdError.WriteLn;
 *)
	  MarkExp(parm,indx);
	  DoParam(parm^.actualX);
	ELSE 
	  DoParam(parm);
	END;
      END; (* while not ended *)
      Release(tide);		(* deallocate all at once here !! *)
    END ParamList;
  (* ------------------------------------------------ *)

  (*
   *  this procedure deals with the set sub-expressions
   *  of binary operators. If "idx" is fxVal, then any
   *  operands which require explicit destinations will
   *  be allocated temporaries. If "idx" indicates that
   *  the operator destination is a temporary, then the
   *  same temporary is reused for whichever of the
   *  operands first is found to need one
   *)
 
  PROCEDURE SetBinOps(exp : ExprDesc;
                      idx : CARDINAL);

    VAR siz    : CARDINAL;
        lTemp  : CARDINAL;
        cls    : ExprNodeClass;
        rIsTmp, lIsTmp : BOOLEAN;

    PROCEDURE Right(rOp : ExprDesc);
      VAR rTemp  : CARDINAL;
    BEGIN
      Alloc(CHR(wordSize-1),siz,rTemp);
      SetExpr(rOp,rTemp);
      DeAlloc(siz);
    END Right;

  BEGIN
    siz := exp^.leftOp^.exprType^.size;
    (*
     *  evaluate attribute and fix left operand
     *)
    cls := exp^.leftOp^.exprClass;
    IF cls IN allLts THEN OtherExpr(exp^.leftOp) END;
    lIsTmp := cls IN tmpCls;
    (*
     *  evaluate attribute and fix right operand
     *)
    cls := exp^.rightOp^.exprClass;
    IF cls IN allLts THEN OtherExpr(exp^.rightOp) END;
    rIsTmp := cls IN tmpCls;

    IF idx = fxVal THEN (* can't reuse as temp *)
      IF lIsTmp THEN
        (*
         *  note that the left temporary cannot be released until
         *  after the right operand tree has been traversed, else
         *  both operands could try to share the same temporary
         *)
        Alloc(CHR(wordSize-1),siz,lTemp); (* release is at !!! *)
        SetExpr(exp^.leftOp,lTemp);
      END;
      IF rIsTmp THEN Right(exp^.rightOp) END;
      IF lIsTmp THEN DeAlloc(siz) END;  (* !!! *)
    ELSE (* destination is temp *)
      IF lIsTmp THEN (* reuse dest for leftOp *)
        SetExpr(exp^.leftOp,idx);
        IF rIsTmp THEN Right(exp^.rightOp) END;
      ELSIF rIsTmp THEN (* reuse dest for rightOp *)
        SetExpr(exp^.rightOp,idx);
      END;
    END;
  END SetBinOps;

  (*
   *  this procedure applies to non-set expressions,
   *  which are implemented by jumping code.
   *)
  PROCEDURE JumpExpr(exp : ExprDesc);
  BEGIN
    IF  (exp^.exprClass = orNode) OR 
	(exp^.exprClass = andNode) THEN
      JumpExpr(exp^.leftOp);
      JumpExpr(exp^.rightOp);
    ELSE
      OtherExpr(exp);
    END;
  END JumpExpr;

  (*
   *  this procedure applies to non-set expressions,
   *  or to sets of word size. It traverses expressions
   *  recursively, allocating temporaries to large set 
   *  constructors and actual params, or operands of relops
   *)
    
  PROCEDURE OtherExpr(exp : ExprDesc);
    VAR size : CARDINAL;
        temp : CARDINAL;
        bool : BOOLEAN;
  BEGIN
    WITH exp^ DO
      CASE exprClass OF
      | preconNode :
	  StatSequence(evalLst); 
          ParamList(theCall^.paramSeq);
      | equalsNode, notEqNode, grEqualNode, lessEqNode :
          (*
           *  operands for these could be sets, so code 
           *  is similar to set binop with fixed result
           *)
          IF IsLargeSet(leftOp) THEN
            SetBinOps(exp,fxVal);
          ELSE
            OtherExpr(leftOp);
            OtherExpr(rightOp);
          END;
      | inNode :
          OtherExpr(leftOp);
          (* 
	   *  rightOp is a set, so ... 
	   *  and all sets need a code-generator temporary
	   *)
          size := rightOp^.exprType^.size;
	  Alloc(CHR(wordSize-1),bytesInWord,temp);
	  MarkExp(exp,temp);
	  IF size > bytesInWord THEN
            IF rightOp^.exprClass IN tmpCls THEN
              Alloc(CHR(wordSize-1),size,temp);
              SetExpr(rightOp,temp);
              DeAlloc(size);
	    ELSE
	      OtherExpr(rightOp);
            END;
          ELSE OtherExpr(rightOp);
          END;
	  DeAlloc(bytesInWord);
      | setDesigNode :
          (* 
	   *  assert: a small set, but must do ranges 
	   *	which usually need a code generator temporary
	   *)
          SetExpr(exp,fxVal); (* a dummy destination *)
      | funcDesigNode :
          ParamList(paramSeq);
      | notNode, negateNode :
          OtherExpr(notOp);
      | castNode :
          IF SetWithTemp(source) THEN
            size := source^.exprType^.size;
            Alloc(CHR(wordSize-1),size,temp);
            SetExpr(source,temp);
            DeAlloc(size);
	  ELSIF ExpWithTemp(source) THEN
            size := source^.exprType^.size;
            Alloc(CHR(wordSize-1),size,temp);
            BigExpr(source,temp);
            DeAlloc(size);
	  ELSE
            OtherExpr(source);
	  END;
      | andNode, orNode :
	  MakeNewCurrent(bools,mergeId);
          JumpExpr(leftOp);
          JumpExpr(rightOp);
      | divNode, starNode, slashNode, modulusNode, remNode,
        plusNode, minusNode, greaterNode, lessNode :
          OtherExpr(leftOp);
          OtherExpr(rightOp);
      | desigNode, adrDesigNode :
          IF NOT EmptySelList(name) THEN
            ScanDesignator(name);
          END;
      | literalNode : FixLiteral(exp);
      | selConstNode :
	  FixLiteral(exp);
	  ScanDesignator(name);
      | errNode :
      END; (* case class of *)
    END; (* with exp^ do *)
  END OtherExpr;

  PROCEDURE SetExpr(exp : ExprDesc;       (* the expression *)
                    idx : CARDINAL);      (* index or fxVal *)
  (* precondition  : exp is desc of a set expression.       *)
  (*                 exp class is IN tmpCls                 *)
  (* postcondition : set constructors and binop nodes, if   *)
  (*                 temporary, have dest. index marked.    *)

      PROCEDURE ScanRanges(seq : Sequence);
        VAR curs : ElemPtr;
            rnge : RangeDesc;
      BEGIN
        InitCursor(seq,curs);
        WHILE NOT Ended(curs) DO
          GetNext(curs,rnge);
          OtherExpr(rnge^.lower);
          IF rnge^.upper <> NIL THEN
            OtherExpr(rnge^.upper);
          END;
        END; (* while *)
      END ScanRanges;

      VAR uTmpIdx   : CARDINAL;

  BEGIN
    IF exp^.exprClass = preconNode THEN
      StatSequence(exp^.evalLst);
      SetExpr(exp^.theCall,idx);
    ELSIF exp^.exprClass = setDesigNode THEN (* set constructor *)
      Alloc(CHR(wordSize-1),bytesInWord * 2,uTmpIdx);
      MarkExp(exp,uTmpIdx);
     (*
      *  large set constructors require an extra temporary
      *  a code generator temporary is always allocated
      *)
      exp^.setConDest := idx; (* whatever it is *)
      ScanRanges(exp^.rangeSeq);
      DeAlloc(bytesInWord * 2);
    ELSIF exp^.exprClass = funcDesigNode THEN
(*
 *	In this context a funcDesigNode does not
 *	need a destination temporary as the set expr
 *	has already allocated one if that is needed
 *)
      MarkExp(exp,idx);			(* no alloc Oct 92 *)
      ParamList(exp^.paramSeq);
    ELSE (* binary ops *)
      exp^.setOpDest := idx;
      SetBinOps(exp,idx);
    END;
  END SetExpr;

  (*
   *  there is an extremely rare, but nevertheless legal case
   *  which necessitates this procedure. A designator _might_
   *  have an index expression which has a function call or a
   *  Boolean expression with a set-valued sub-expression
   *
   *  Furthermore (feb-90) a designator might have an index
   *  expression which accesses a selected constant --- in
   *  this case the constant must have its literal fixed
   *)

  PROCEDURE ScanDesignator(name : DesigRec);
    VAR dstt : DStateType;
        attr : SelectAttribute;
	indx : CARDINAL;
  BEGIN
    InitDState(name,dstt);
    LOOP
      GetSelector(dstt,attr);
      IF attr.tag = endMarker THEN EXIT;
      ELSIF attr.tag = subscriptNode THEN 
	IF isStrIx IN attr.exp^.testFlags THEN
          Alloc(CHR(wordSize-1),bytesInWord,indx);
          MarkExp(attr.exp,indx);
	  OtherExpr(attr.exp);
	  DeAlloc(bytesInWord);
	ELSE 
	  OtherExpr(attr.exp);
	END;
      (* else skip to next *)
      END;
    END;
  END ScanDesignator;

  PROCEDURE BigExpr(exp : ExprDesc;
		    tix : CARDINAL);
  BEGIN
    IF exp^.exprClass = preconNode THEN
      StatSequence(exp^.evalLst);
      BigExpr(exp^.theCall,tix);
    ELSIF exp^.exprClass = funcDesigNode THEN
      MarkExp(exp,tix);
      ParamList(exp^.paramSeq);
    ELSIF exp^.exprClass = constructorNode THEN
      exp^.setConDest := tix;
      RangeSequence(exp,tix);
    ELSIF exp^.exprClass = setDesigNode THEN
      SetExpr(exp,tix);
    ELSE Assert(FALSE,"bad exprClass");
    END;
  END BigExpr;

  PROCEDURE RangeSequence(exp : ExprDesc;
			  bas : INTEGER);	(* Oct-92 *)
    VAR rCurs  : ElemPtr;
	rElem  : RangeDesc;
	index  : CARDINAL;
  BEGIN
    Alloc(CHR(wordSize-1),bytesInWord,index);
    MarkExp(exp,index);
    InitCursor(exp^.rangeSeq,rCurs);
    WHILE NOT Ended(rCurs) DO
      GetNext(rCurs,rElem);
      WITH rElem^ DO
	IF upper <> NIL THEN 
	END;
	IF SetWithTemp(lower) THEN
	 (*
	  *  This next ensures that any constructed set
	  *  is constructed in the destination location
	  *)
	  SetExpr(lower,bas + elemOffset);
        ELSIF ExpWithTemp(lower) THEN
	 (*
	  *  In this context a funcDesigNode does not
	  *  need a destination temporary as the caller
	  *  has already allocated one
	  *)
	  BigExpr(lower,bas + elemOffset);
	ELSE OtherExpr(lower);
	END;
      END;
    END;
    DeAlloc(bytesInWord);
  END RangeSequence;

  (* ----------------------------------------------------- *
   *  this procedure scans statement sequences recursively,
   *  traversing any expression which are encountered
   * ----------------------------------------------------- *)

  PROCEDURE StatSequence(seq : Sequence);
    VAR statCurs, spareCurs : ElemPtr;
        statement : StatDesc;
        caseElem  : CaseDesc;
        ifElem    : IfDesc;
	index,siz : CARDINAL;
        inclOrExcl: BOOLEAN;
	forHasTmp : BOOLEAN;
  BEGIN
    InitCursor(seq,statCurs);
    WHILE NOT Ended(statCurs) DO
      GetNext(statCurs,statement);
      WITH statement^ DO
        CASE statClass OF
        | compoundNode :
	    StatSequence(inlineBody);
        | assignNode :
	    ScanDesignator(designator);
	    IF  NOT ExpWithTemp(expression) AND
	        NOT SetWithTemp(expression) THEN
	      OtherExpr(expression);
	    ELSIF expression^.exprClass IN cnOrFn THEN
	      (* functions and constructors *)
	      (* arrays, records _and_ sets *)
	      siz := expression^.exprType^.size;
              Alloc(expression^.exprType^.alignMask,siz,index);
	      BigExpr(expression,index);
	      DeAlloc(siz);
	    ELSE (* set binops *)
	      SetExpr(expression,fxVal);
	    END;
        | caseNode :
	   (*
	    *  case statements need a temporary for
	    *  storing the switch expression (kjg 94)
	    *)
	    Alloc(CHR(wordSize-1),bytesInWord*2,index);
	    MarkStat(statement,index);
	    OtherExpr(caseInfo^.switch);	(* kjg 20-Jun-91 *)
            InitCursor(cases,spareCurs);
            WHILE NOT Ended(spareCurs) DO
              GetNext(spareCurs,caseElem);
              StatSequence(caseElem^.statSeq);
            END;
            StatSequence(default);
	    DeAlloc(bytesInWord*2);
        | ifNode :
            InitCursor(branches,spareCurs);
            WHILE NOT Ended(spareCurs) DO
              GetNext(spareCurs,ifElem);
              IF ifElem^.condition <> NIL THEN
                OtherExpr(ifElem^.condition);
              END;
              StatSequence(ifElem^.statSeq);
            END;
        | whileNode, repeatNode :
            OtherExpr(condition);
            StatSequence(wrBody);
        | forNode :
	    forHasTmp := (final^.exprClass <> literalNode) OR
			 (initial^.exprClass <> literalNode);
	    IF forHasTmp THEN
	      Alloc(CHR(wordSize-1),bytesInWord * 2,index);
	      MarkStat(statement,index);
	    END;
            OtherExpr(initial);
            OtherExpr(final);
            StatSequence(forBody);
	    IF forHasTmp THEN
	      DeAlloc(bytesInWord * 2);
	    END;
        | withNode :
	    WITH withInfo^ DO
              ScanDesignator(desig);
	      (*
	       *   now, is a code-generator temporary needed ?
	       *)
	      IF desig.variable <> dummy THEN
	        Alloc(CHR(wordSize-1),bytesInWord,index);
		MarkStat(statement,index);
                StatSequence(withBody);
		DeAlloc(bytesInWord);
	      ELSE
                StatSequence(withBody);
	      END;
	    END;
        | returnNode :
            IF returnResult <> NIL THEN
            (* 
             *   CURRENTLY, functions do not return large
             *   sets, but later this test might succeed
	     *
	     *   18-Sep-92 ... and now they do ... kjg
	     *   in this case the result is now computed in the destination
	     *)
              IF SetWithTemp(returnResult) THEN
		SetExpr(returnResult,fxVal);
              ELSIF ExpWithTemp(returnResult) THEN
	  	BigExpr(returnResult,03H);	(* index is not needed *)
              ELSE OtherExpr(returnResult);
              END;
            END;
        | procCallNode : 
          (*  If set INCL or EXCL allocate a temporary   *)
            IF designator.variable^.idClass = stProc THEN
	      IF (designator.variable^.procVal = inclP) OR
                 (designator.variable^.procVal = exclP) OR 
                 (designator.variable^.procVal = resetP) THEN 
                Alloc(CHR(wordSize-1),bytesInWord,index);
	        MarkStat(statement,index);
                ParamList(actualParams);
                DeAlloc(bytesInWord);
	      ELSIF (designator.variable^.procVal = newP)  OR
                    (designator.variable^.procVal = appendP) THEN
                Alloc(CHR(wordSize-1),bytesInWord * 4,index);
	        MarkStat(statement,index);
                ParamList(actualParams);
                DeAlloc(bytesInWord * 4);
	      ELSE
                ParamList(actualParams);
	      END;
            ELSE
              ParamList(actualParams);
            END;
        | loopNode     : StatSequence(loopBody);
        | exitNode, emptyNode, retryNode : (* nothing *)
        END; (* case statClass *)
      END; (* with statement^ *)
    END; (* while *)
  END StatSequence;

  PROCEDURE MarkSetExpressions(proc : IdDesc);
    VAR size : CARDINAL;
  BEGIN
    InitCount();
    current := proc;
    StatSequence(proc^.body^.statements);
    StatSequence(proc^.body^.finalSeq);
    StatSequence(proc^.body^.exceptSeq);
    StatSequence(proc^.body^.finalExSeq);
    size := HiTide();
    IF size > proc^.frame^.body^.tempSize THEN 
      proc^.frame^.body^.tempSize := size;
    END;
  END MarkSetExpressions;

END M2SetTemporaries.

