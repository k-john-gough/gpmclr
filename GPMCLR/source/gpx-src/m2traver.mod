(****************************************************************)
(*                                                              *)
(*              Modula-2 Compiler Source Module                 *)
(*                                                              *)
(*            Tree Traversal and Semantic Checking              *)
(*                                                              *)
(*      (c) copyright 1988 Faculty of Information Technology    *)
(*                                                              *)
(*      original module : May 1988                              *)
(*      modifications   : fix att. for call of ext. procVar     *)
(*                        10 Aug 88 JRH Actual parameter checks *)
(*                        24 Aug 88 JRH More expr result types  *)
(*                        25 Aug 88 JRH ActualParMode           *)
(*                        07 Sep 88 JRH Unary & binary ops      *)
(*                        14 Sep 88 JRH Set designator node     *)
(*                        01 Nov 88 kjg Fix bug in S1 coercion  *)
(*                        04 Nov 88 jrh Set desig builds union  *)
(*                        16 Nov 88 jrh Standard procedures     *)
(*                        30 Dec 88 jrh Loop validation         *)
(*                        18 Jan 89 kjg Mv FixLit. to M2SetTem. *)
(*                        22 Jan 89 kjg fix minP, maxP for chrs *)
(*                        28 Jan 89 kjg complete castP and valP *)
(*                                      fix empty set construct *)
(*                        14 Feb 89 jrh set constr range checks *)      
(*                                  jrh RETURN EXITs from LOOP  *)
(*                        20 Feb 89 jrh Index & range checks    *)
(*                        22 Feb 89 jrh No selectors on type    *)
(*                        24 Feb 89 jrh Add timeP & exitP       *)
(*                        11 Mar 89 jrh Resolve var formals     *)
(*			  23 Mar 89 kjg Add abortP, newP, disP	*)
(*			  25 Mar 89 kjg assign comp. for array	*)
(*					indices, mod. for-loops *)
(*			  24 May 89 jrh enable NEW & DISPOSE    *)
(*			  26 May 89 jrh amorphous open arrays   *)
(*			  10 Jun 89 kjg more casts and tests    *)
(*			  11 Jun 89 kjg new system procs, funcs *)
(*			  13 Jun 89 jrh error 243 on local proc *)
(*			  14 Jun 89 jrh INC/DEC CheckFORThreat  *)
(*			  14 Jun 89 jrh relax HasAddress check  *)
(*			  14 Jun 89 jrh size & align FOR cv tmp *)
(*			  20 Jun 89 jrh ChkFORThr before compat *)
(*			  27 Jun 89 jrh / REM DIV MOD logic     *)
(*			   4 Aug 89 kjg sizeP returns ZZ	*)
(*			   4 Aug 89 kjg adrP threatens for var  *)
(*			   4 Aug 89 kjg errs 296..7 FOR threats *)
(*			  17 Aug 89 jrh -ve rOp now ok for DIV  *)
(*			  24 Aug 89 kjg new system proc callP	*)
(*			  04 Sep 89 jrh checks on ABS, FLOAT    *)
(*			  02 Oct 89 jrh checks on TRUNC         *)
(*			  16 Oct 89 kjg Warning495 added	*)
(*			  17 Oct 89 kjg Fix AND and OR typetest *)
(*			  26 Oct 89 kjg forceIxTst for opens    *)
(*			   9 Nov 89 kjg tests for constructors  *)
(*			  30 Nov 89 kjg IRIS code moved back    *)
(*			  27 Feb 90 kjg all calls now in adjBlk *)
(*			  17-Mar 90 highExp get empty testFlags *)
(*			  23-Mar-90 kjg calls of inline mods    *)
(*					are appended to current *)
(*		          15-Apr-90 kjg param sizes are eval'd. *)
(*					Remove 27-Feb modif	*)
(*			  16-Apr-90 kjg newp ==> nonLeafProc    *)
(*			  10-May-90 kjg CheckCallPars with PROC *)
(*			  13-Jun-90 kjg Error 319 for attempted *)
(*					assignment to open arrs *)
(*			   9-Jul-90 kjg fix to type in construc *)
(*			  11-Sep-90 kjg put early return in NEW *)
(*			  19-Oct-90 kjg improve withs of params *)
(*			  23-Oct-90 kjg fix size, FOR anon type *)
(*			   2-Nov-90 kjg adrP processing for FOR *)
(*			  20-Nov-90 kjg final exp of FOR compat *)
(*			  10-Dec-90 kjg limit flt <-> wrd casts *)
(*                        09-May-91 jrh size of string literals *)
(*			  14-Jul-91 kjg fix FLOAT of subranges  *)
(*			  16-Jul-91 kjg resolved type of formal *)
(*			  15-Apr-92 jrh BindDesignator endMarkr *)
(*			  15-Apr-92 kjg ErrIdent for 233	*)
(*			  30-May-92 jrh Float int or fixValue	*)
(*			  25-Aug-92 kjg fix RecordCallOf flds   *)
(*			  21-Sep-92 kjg fix tyClass of fp cons  *)
(*			  15-Nov-92 kjg check FOR limit test    *)
(*								*)
(*   =============== merged mips and i386 source ============	*)
(*			   kjg 22 Mar 93			*)
(*								*)
(*	modifications:    23-Mar-93 kjg maxPar set for procVars *)
(*                                                              *)
(*                   : Update 2003, for CLR version. All code   *)
(*                     following "emitCil" tests.  kjg          *)
(*                                                              *)
(****************************************************************
$Log: m2traver.mod,v $
Revision 1.42  1997/03/16 06:41:42  hynd
John Hynd, for KJG: Replace body=NIL fix (ineffective for interface modules) 
with NOT(defMod IN modState) guard

Revision 1.41  1997/02/24 03:50:24  behrooz
modified procedures MakeCast and TraverseExp to fix John Lancaster's bugs.

Revision 1.40  1997/01/16 05:28:37  gough
        new procedures TraversePrecon, CheckPrecon.
        Some other detailed changes to TraverseExp.

Revision 1.39  1996/11/27 03:15:03  lederman
allocate exception descriptors, set varParThreat in BindDesignator() if var
referenced in both normal and except parts and add traversals for except seqs.

Revision 1.38  1996/11/14 04:48:11  gough
set the isStrIx flag for string subscript index expressions

Revision 1.37  1996/09/20 08:07:19  lederman
fix up handling of wrong number of params in newP/disP
also appendClass now in StatDesc of appendP

Revision 1.36  1996/09/19 08:09:10  lederman
APPEND now sets up .appendClass in second params typeDesc so we get it right later

Revision 1.35  1996/09/13 01:37:41  lederman
check for NIL type on valP

Revision 1.34  1996/08/28 23:01:30  gough
create dummy errNode for high for ALL strings going to open formals

Revision 1.33  1996/08/20 01:42:07  lederman
require size param. of NEW (STRING) to be assign compatible with ints

Revision 1.32  1996/08/07 23:44:58  gough
semantic checks for CUT
also second param for all string procedures now protected with ty=NIL test

Revision 1.31  1996/08/07 07:54:29  gough
make sure that procedures which call CONCAT have room for five params
in the parameter assembly area.  (__SSCATST__ uses five params)
Also, ensure that MakeWrapper() is passed the correct type descriptor

Revision 1.29  1996/08/07 01:50:44  lederman
HIGH for STRING must return int type

Revision 1.28  1996/08/07 01:44:19  lederman
check for error return from TraverseExp() in VAL()

Revision 1.27  1996/08/06 23:45:30  gough
do construction necessary for creation of wrapper procedures, used when
passing STRING OF T types to open ARRAY OF T value parameters.

Revision 1.25  1996/07/30 00:03:47  gough
type check APPEND and CONCAT, and overloaded NEW and DISPOSE.

Revision 1.24  1996/01/08 05:31:52  gough
set hiDesc to enable elimination of some open array index tests,
use INCLs everywhere for variable attribute tracking

Revision 1.23  1995/10/27 05:57:30  lederman
partial fix to VAL(HUGEINT,) - really has to wait for 64-bit compiler

Revision 1.22  1995/10/18 00:48:49  lederman
maxP extended to float & double types
chrP of literals fixed to set stringHigh = 1
/ 0 seperated from / 0.0 case which gives new warning 511

Revision 1.21  1995/10/10 23:58:56  lederman
DCode V3 HugeInt stuff

Revision 1.20  1995/09/28 04:31:22  lederman
Swap errors 313 & 314 for array constructors

Revision 1.19  1995/09/21 06:17:19  gough
make constant CHRs return PointerTo(S1) rather than PointerTo(chars)

Revision 1.18  1995/09/15 08:02:06  gough
Ensure that for loops which need an anon variable get one.

# Revision 1.17  1995/05/11  06:02:56  gough
# allow casts of wordsized literal sets to other wordsized objects
#
# Revision 1.16  1995/05/02  02:02:05  lederman
# Set varClass of marshalling temporary to 'auto'
#
# Revision 1.15  1995/03/28  22:57:28  gough
# nicer code for absP, making sure that folded literals are either ZZ or RR
#
# Revision 1.14  1995/03/27  08:05:40  gough
# make absP fold literal expressions.
#
# Revision 1.13  1995/03/27  01:23:25  gough
# fix error in code of CreateByteHigh in one-open-dimension case
#
# Revision 1.12  1995/03/24  08:24:27  gough
# fix up error in openByteHigh for fixed array size ...
#
# Revision 1.11  1995/03/23  23:10:21  gough
# many changes relating to the inclusion of multidimensional open arrays,
# and their semantic tests.
#
# Revision 1.10  1995/03/17  03:52:11  gough
# ensure that expressions without an address _always_ get a cast temporary
#
# Revision 1.9  1995/03/17  02:13:32  gough
# Fix HasAddress to exclude variables which might be in registers.
# Set varClass on loopJunk variables.
# Simpler expression for needTmp in MakeCast.
#
# Revision 1.8  1995/03/14  07:37:33  gough
# violation of valP rules now leads to error 218 rather than 206
#
# Revision 1.7  1995/03/14  07:27:48  gough
# valP must check that the second param is ordinal or numeric!
#
# Revision 1.6  1995/03/14  01:56:21  gough
# Many changes:
#    Marshalling of open arrays on the caller side
#    Loosening of constraints on assignment to BYTE and WORD
#    New non-standard warning message 494 (once only unless "-v")
#
# Revision 1.5  1995/03/02  08:56:17  gough
# creation and attribution of castNode node type
#
# Revision 1.4  1995/02/20  02:55:47  gough
# mark cast objects which need to be in memory, so that they have the
# address taken flag ==> they will be in memory.
#
# Revision 1.3  1995/02/13  22:54:05  gough
# tag all cast variables with the varParThreat attribute ==> can't be in reg.
#
# Revision 1.2  1995/01/05  05:41:39  gough
# clean up semantics of castP, to stop entire access to open arrays
# and remove arbitrary restriction on use of float in native code versions.
#
# Revision 1.1  1994/11/30  01:45:28  lederman
# Initial revision
#
*****************************************************************
# Revision 1.4.3.1  1994/11/29  07:01:32  gough
# fix up bad compatibility check in exitP, should be AssignCompat
#
# Revision 1.5  1994/10/21  07:12:07  gough
# second param of INCL/EXCL should be _assign_compatible only!
#
# Revision 1.4  1994/07/01  05:52:15  lederman
# clear constant constructors after allocation so pads are clean
#
# Revision 1.3  1994/06/27  23:21:38  lederman
# fix up checking of UnivConform with value parameters.
#
# Revision 1.2  1994/04/21  06:29:43  lederman
# Remove bootstrap comment around ROUND and ENTIER code
#
# Revision 1.1  1994/04/07  05:29:52  lederman
# Initial revision
*****************************************************************
Revision 1.22  94/03/29  17:22:06  gough
fix up exact limits for wholeNum <-- floatNum compile-time conversions
intP, truncP, valP, entierP, roundP have all been affected

Revision 1.18  94/03/17  10:44:08  gough
some changes caused by new interface to allow traversal of const defs.

Revision 1.17  94/02/18  09:06:12  gough
give warning 510 for non-wg13 permitted uses of VAL

Revision 1.16  94/02/17  08:24:39  gough
insert new ISO functions INT, and extend VAL to do real <--> int conversions
new (non-standard) system functions ENTIER and ROUND
complete changeover to ADDADR from INCADR etc.
convert ROTATE and SHIFT to function procedures (with back compat.)

Revision 1.15  93/10/11  13:39:02  gough
clean of of last mods, more careful computation of cvTmp range limits

Revision 1.14  93/10/08  13:53:48  gough
revision of semantic checks for upper bounds of for loops

Revision 1.13  93/10/06  11:50:40  gough
fixing up for loop upper bounds finally (whimper, whimper)

Revision 1.12  93/09/21  15:41:49  gough
put range test on constants in INCL and EXCL

Revision 1.11  93/08/09  11:00:08  gough
fix up literal DIV by negatives to give error 295

Revision 1.10  93/08/05  11:55:00  gough
remove range tests on constants on lhs of IN expressions

Revision 1.9  93/07/21  16:38:59  gough
array index expressions now are marked with exprType = expression
type rather than the previous exprType = index type

Revision 1.8  93/07/20  13:52:21  gough
make sure that FOR loop literal upper bounds get range checked at compile
time against actual type, runtime range check against hostType is OK

Revision 1.7  93/07/09  14:26:05  gough
fix up literals in the tree with "- <maxInt + 1>"

Revision 1.6  93/06/08  15:10:20  mboss
change for loop upper bound error to 324

Revision 1.5  93/06/03  12:20:12  mboss
insert extra test for threats to for loop control vars from nested fors

Revision 1.4  93/06/03  12:12:18  mboss
fix up for loop final value test type

Revision 1.3  93/05/25  11:57:05  goughh
installing log

Revision 1.2  93/05/24  14:57:40  gough
fix of error where a WITH statement obscures the local
variable which is the control variable of a FOR statment
*****************************************************************)

IMPLEMENTATION MODULE M2Traversal;

  IMPORT StdError, M2CilWrappers, M2DcfWrappers;

  FROM GenSequenceSupport IMPORT IsEmpty, GetFirst, LinkRight, LinkLeft,
        Sequence, Ended, ElemPtr, InitCursor, InitSequence, GetNext, 
        NextIsLast, DisposeList, LengthOf;

  FROM M2Alphabets IMPORT
        TerminalSymbols, LexAttType, ModStateFlags, ModStateSet, Flags,
	errors, Spellix, FlagSet, ConBlock, HashBucketType;

  FROM M2NodeDefs IMPORT
	UsesSet, VarUses, InsertRef, LoopJunk,
        IdDesc, IdRec, IdNodeClass, 
	IdString, codeBlkList,
	StrucTree, StrucRec,
        TypeDesc, TypeRec, TyNodeClass, IdTree, CreateTypeDesc,
        Attribute, AttributeSet, StandardProcs,
        modState, CreateIdDesc,
        current, thisCompileUnit,
        IdClassSet, TyClassSet, infinity,
	FormalClass, FormalType, MakeFormal;

  FROM M2StructureDefs IMPORT StatDesc, StatRec, StatNodeClass, 
        RangeDesc, RangeRec, CaseStatDesc, CaseStatRec,
	MakeRangeDesc, CreateStatDesc,
        CaseDesc, CaseRec, IfDesc, IfRec;

  FROM M2Designators IMPORT 
	InitDState, DStateType, CloneDesig,
	InitDesignator, ExpandInfo,
        ExprDesc, CreateExprDesc, ExprRec, ExprNodeClass, WithDesc,
        EmptySelList, MaxCacheIndex, SelectNodeClass,
        MoveSelectors, GetSelector, SelectAttribute,
        DesigRec, AccessMode, SetAccessMode, BindFieldName,
        ActualParMode, AccessModeOf, ForceAccessMode;

  FROM M2InOut IMPORT Error, ErrIdent, DiagName, lastPos, Position;

  FROM M2SSUtilities IMPORT SetCurrentScope, Lookup,
	LookupInThisScope, MinOfOrdType, MaxOfOrdType,
        IsVariable, CheckValidAllocate, FixTypeAndValue,
        UnivConform, CheckedAssignCompatible, 
	ValOpenCompatible, VarOpenCompatible, 
        IsOrdinalType, OrdinalValue, Compatible, IsSignedType,
        IndexCardinality, IndexCheckC, RangeCheckC, 
	LoadGlobals, TypesOverlap, LiteralInRange;

  FROM M2CompOperations IMPORT Negate, Operation,
	CopyConstant, ExtractCon (* ! , BoolOps*);

  FROM M2CaseSelectors IMPORT FindMinAndMax;
  FROM M2Scanner       IMPORT CurrentFlags;
  FROM M2TabInitialize IMPORT PointerTo, CastIdDesc, PreconIdDesc;
  FROM M2MachineConstants IMPORT 
	wordSize, charMax, cardMax, bitsInWord, bigEndian, oP5, bytesInWord;

  FROM M2NameHandler IMPORT MakeEmptySet, Commit, SetInclude,
        StringTable, SetRngIncl, anonBkt, allocBkt, deallBkt;

  FROM SYSTEM IMPORT ADR, CAST, TSIZE, ADDRESS, ENTIER, ROUND;
  FROM Storage IMPORT ALLOCATE, DEALLOCATE;
  FROM ProgArgs IMPORT Assert;
  FROM Types    IMPORT Card32;

  FROM M2NamGenerate IMPORT MakeTempName, MakeNewCurrent;

  FROM M2ProcState IMPORT FormalSize;

  TYPE ExClassSet = SET OF ExprNodeClass;
  TYPE ActualModeSet = SET OF ActualParMode;
  TYPE LoopStatus = (notInLoop, noExitYet, exited, returned);
                    (* returned is superset of exited - propagates to 
                       enclosing loops *)

  TYPE  ExceptStates = (noExcept, inNormal, inExcept);
  VAR   exceptState  : ExceptStates;

  TYPE   AccessSet  = SET OF AccessMode;
  CONST  anyUplevel = AccessSet{directNonL,uplevel,uplevelIndirect};
	 noTests    = FlagSet{};
	 ixOnly     = FlagSet{indexTests};

  VAR activeControls : Sequence;       (* active FOR loop control variables *)
      castPtr        : IdDesc;         (* substitution for type transfers   *)
      chTyPtr, crdTyPtr, intTyPtr, adrTyPtr, boolTyPtr : TypeDesc;
      rrTyPtr, fltTyPtr, dblTyPtr, hugeTyPtr, setTyPtr : TypeDesc;
      lengthFormals, newAssertFrms, oldAssertFrms : Sequence;

  CONST realSet = TyClassSet{RR,floats,doubles};
	litSets = TyClassSet{II,UU,ZZ,RR};
	iNumVar = TyClassSet{ints,cards};
	iNumVal = iNumVar + TyClassSet{II,ZZ,UU};
	wg13Num = iNumVal + realSet;
	numeric = wg13Num + TyClassSet{hInts};

  CONST mtSeq = Sequence{NIL,NIL};
  VAR   callPos     : Position;

(* ---------------------------------------------------------------- *) 
(*
   This module provides for warnings of obsolete standard functions
   or procedures which are about to be changed for the next release.
   It gives the warning only for the first of each such usages
 *)
(* ---------------------------------------------------------------- *) 
  MODULE ObsoleteWarning;
    IMPORT Error, StandardProcs;
    EXPORT Warning495, Warning494;

    VAR warned : ARRAY StandardProcs OF BOOLEAN;
	index  : StandardProcs;
	warn494 : BOOLEAN;

    PROCEDURE Warning494;
    BEGIN
      IF NOT warn494 THEN
	Error(494); warn494 := TRUE;
      END;
    END Warning494;

    PROCEDURE Warning495(stp : StandardProcs);
    BEGIN
      IF NOT warned[stp] THEN
	Error(495); warned[stp] := TRUE;
      END;
    END Warning495;

  BEGIN
    warn494 := FALSE;
    FOR index := MIN(StandardProcs) TO MAX(StandardProcs) DO
      warned[index] := FALSE;
    END;
  END ObsoleteWarning;
(* ---------------------------------------------------------------- *) 

(* ---------------------------------------------------------------- *) 
  PROCEDURE ExpErr(exp : ExprDesc; err : CARDINAL);
  BEGIN
    lastPos := exp^.sourceLoc; Error(err);
  END ExpErr;

  PROCEDURE Error216(actualParamCursor : ElemPtr);
  (*
    Output error 216 - too many parameters - on the first excess parameter.
    Also check the excess parameters for internal errors.
  *)
  VAR excessExpr : ExprDesc;
  BEGIN
    GetNext(actualParamCursor,excessExpr);
    ExpErr(excessExpr,216); (* source location now correct *)
    LOOP
      TraverseExp(excessExpr);
      IF Ended(actualParamCursor) THEN EXIT;
      ELSE GetNext(actualParamCursor,excessExpr);
      END;
    END;
  END Error216;
      
(* ------------------------------------------------------------------------ *) 

PROCEDURE IsFORThreat (affected : IdDesc) : BOOLEAN;
(*
   Pre-condition: affected is non-NIL, and is a varNode;
   Check if it matches any active FOR loop control variable -
   these are held on the global Sequence activeControls.
*)
VAR curs : ElemPtr;
    element : IdDesc;
BEGIN
  IF NOT IsEmpty(activeControls) THEN
    GetFirst(activeControls,curs,element);
    LOOP
      IF element=affected THEN
(*      Error(279); *)
        RETURN TRUE;
      ELSIF Ended(curs) THEN EXIT;
      ELSE GetNext(curs,element);
      END;
    END;
  END;
  (* Affected is not a control variable *) 
  RETURN FALSE;
END IsFORThreat;

PROCEDURE HasAddress(ex : ExprDesc) : BOOLEAN;
(* returns true if object has a storage address *)
  VAR class : TyNodeClass;
BEGIN (* assert: ex has been traversed *)
  class := ex^.exprType^.tyClass;
  RETURN (class = SS) OR			(* any string   *)
	 (class = arrays) OR			(* any array    *)
	 (class = records) OR			(* any record   *)
         ((class = sets) AND 			(* literal set  *)
	  ((ex^.exprClass = literalNode) OR	(* any big set  *)
	   (ex^.exprType^.size > wordSize))) 
(*
 *	OR
 *	 ((ex^.exprClass = desigNode) AND 	(* any variable *)
 *	  (ex^.name.variable^.idClass = varNode));
 *)
END HasAddress;

(*
 * --------------------------------------------------------------------------
 *  CheckActualParam has been moved outside CheckActualParamList (kjg Apr 90)
 *  so that it may be called from the new procedure CheckDirectParamList
 *  for the new interface to C. This new procedure does NOT add high values
 * --------------------------------------------------------------------------
 *)

  PROCEDURE GetOpenInfo(exp : ExprDesc;
		    VAR opN : CARDINAL;
		    VAR typ : TypeDesc);
  BEGIN
   (*
    *  exp is the actual expression, we want to return
    *  the number of open dimensions, and the elemType.
    *)
    opN := 0;
    typ := exp^.exprType;
    WHILE (typ^.tyClass = arrays) AND typ^.isDynamic DO
      INC(opN);
      typ := typ^.elementType;
    END;
  END GetOpenInfo;

  PROCEDURE CheckPrecon(apSq : Sequence; 	(* actual param sequence *)
		        preT : ExprDesc;	(* pre. expr in TypeDesc *)
		    VAR stSq : Sequence);	(* incidental statements *)

    PROCEDURE ParamN(s : Sequence; i : CARDINAL) : ExprDesc;
      VAR curs : ElemPtr;
	  elem : ExprDesc;
	  pIdx : CARDINAL;
    BEGIN
      InitCursor(s,curs);
      FOR pIdx := 1 TO i DO 
	GetNext(curs,elem); 
        IF elem = NIL THEN RETURN NIL END;
      END;
      RETURN elem;
    END ParamN;

    PROCEDURE Clone(example : ExprDesc; VAR instance : ExprDesc);
      VAR temp : ExprDesc;
    BEGIN
      IF example = NIL THEN temp := NIL; 
      ELSE
	CreateExprDesc(temp,errNode); temp^ := example^; (* clone *)
	IF example^.exprClass <= negateNode THEN
          Clone(example^.leftOp,temp^.leftOp);
	  IF example^.exprClass <= inNode THEN
            Clone(example^.rightOp,temp^.rightOp);
	  END;
	ELSIF example^.exprClass = funcDesigNode THEN
	  CloneParams(example^.paramSeq,temp^.paramSeq);
	ELSIF (example^.exprClass = setDesigNode) OR
	    (example^.exprClass = constructorNode) THEN
	  CloneRanges(example^.rangeSeq,temp^.rangeSeq);
	ELSIF example^.exprClass = desigNode THEN
	  CloneDesig(example^.name,temp^.name);
	  CheckDesig(temp);
	END;
      END;
      instance := temp;
    END Clone;

    PROCEDURE CloneParams(ex : Sequence; VAR in : Sequence);
      VAR curs : ElemPtr;
	  parm : ExprDesc;
	  copy : ExprDesc;
    BEGIN
      InitSequence(in);
      InitCursor(ex,curs);
      WHILE NOT Ended(curs) DO
	GetNext(curs,parm);
	Clone(parm,copy);
	LinkRight(in,copy);
      END;
    END CloneParams;

    PROCEDURE CloneRanges(ex : Sequence; VAR in : Sequence);
      VAR curs : ElemPtr;
	  rnge : RangeDesc;
	  loEx : ExprDesc;
	  hiEx : ExprDesc;
    BEGIN
      InitSequence(in);
      InitCursor(ex,curs);
      WHILE NOT Ended(curs) DO
	GetNext(curs,rnge);
	Clone(rnge^.lower,loEx);
	Clone(rnge^.upper,hiEx);
	LinkRight(in,MakeRangeDesc(loEx,hiEx));
      END;
    END CloneRanges;

    PROCEDURE CheckDesig(VAR exp : ExprDesc);
     (* 
      *  Initially at least exp is a desigNode, being 
      *  a leaf node in a cloned precondition expression.
      *)
      VAR temp  : StatDesc;
	  state : DStateType;
	  attri : SelectAttribute;
	  posEx : ExprDesc;
	  rhsEx : ExprDesc;
	  newI  : IdDesc;
	  ok    : BOOLEAN;
    BEGIN
      IF exp^.name.variable^.idClass = posParNode THEN
	posEx := ParamN(apSq,exp^.name.variable^.posIndex);
       (*
	*  There are three cases here:
	*  --	the actual param is an entire variable
	*	==> leave the actual untouched, and
	*	    make the leaf select the same var.
	*  --	the actual is not an entire variable
	*	==> evaluate the actual into a temp,
	*	    and make param and leaf point to it.
	*  --   the actual param is a literal
	*	==> leave the actual untouched,
	*	    make the leaf be the same literal.
	*)
	IF (posEx^.exprClass = desigNode) AND 
	    EmptySelList(posEx^.name) THEN 
	 (*
	  *  This is a reference to an entire variable.
	  *  In this case we just copy the reference and
	  *  the access mode.  Beware that exp^ may have
	  *  further selectors.
	  *)
	  exp^.name.variable := posEx^.name.variable;
	  ForceAccessMode(exp^.name, AccessModeOf(posEx^.name));
	ELSIF posEx^.exprClass = literalNode THEN
	 (* change the desigNode to a literal *)
	  Assert(EmptySelList(exp^.name));
	  exp^ := posEx^;
	ELSE
	 (*
	  *  This is a not an entire variable.
	  *  We create a temporary variable, and
	  *  change both references to point to that.
	  *)
	  CreateStatDesc(temp,assignNode);
	  CreateIdDesc(anonBkt,newI,varNode);
	  MakeTempName(newI);
	  InsertRef(current^.scope, newI, ok);
	  newI^.varType := posEx^.exprType;
	  CreateExprDesc(rhsEx,errNode); rhsEx^ := posEx^; (* clone *)
          temp^.designator.variable := newI;
	  temp^.desigType := posEx^.exprType;
	  temp^.expression := rhsEx;
	  ForceAccessMode(temp^.designator,directLocl);
	  exp^.name := temp^.designator;
	  posEx^.exprClass := desigNode;
	  posEx^.name := temp^.designator;
	  LinkRight(stSq,temp);
	END;
      END;
      IF (exp^.exprClass = desigNode) AND
	 NOT EmptySelList(exp^.name) THEN
	InitDState(exp^.name,state);
	REPEAT
	  GetSelector(state,attri);
	  IF attri.tag = subscriptNode THEN
	    Clone(attri.exp, attri.exp); (* overwrite in place *)
	  END;
	UNTIL attri.tag = endMarker;
      END;
    END CheckDesig;

    VAR cond : StatDesc;
	preI : ExprDesc;		(* pre. expr instance *)

  BEGIN (* CheckPrecon *)
    IF CurrentFlags() * errors <> FlagSet{} THEN RETURN END;
   (*
    *  Make an instance of the precondition expression,
    *  with the actual parameters substituted for posPars.
    *  Note that Clone() has the side-effect of finding
    *  any computations which need to be done first, and
    *  putting generating assignments on the stSq list.
    *)
    Clone(preT,preI);
    preI^.sourceLoc := lastPos;
    TraverseExp(preI);  (* so as to fold lits *)
   (* create precond assert call *)
    lastPos := callPos;
    IF preI^.exprClass = literalNode THEN
      IF preI^.conValue.fixValue = ORD(FALSE) THEN Error(493) 
			ELSIF verbose IN modState THEN Error(492); END;
    ELSIF verbose IN modState THEN Error(491);
    END;
    CreateStatDesc(cond,procCallNode);
    cond^.designator.variable := PreconIdDesc();
    LinkRight(cond^.actualParams,preI);	(* the only parameter *)
    LinkRight(stSq,cond);
  END CheckPrecon;

  PROCEDURE CheckActualParam (VAR needWr : BOOLEAN;
			      VAR actual : ExprDesc;
				  formal : FormalType);
  (*
   *  Check a single actual parameter against its formal; if formal is var,
   *  and actual is a variable, change actual to a refActual access.
   *)
  
    PROCEDURE CreateLoopJunk(expr : ExprDesc);
      VAR lj : LoopJunk;
    BEGIN
      IF current^.body^.loopJunk = NIL THEN
	NEW(lj);
	current^.body^.loopJunk := lj;
	MakeNewCurrent(adrs,lj^.src);
	MakeNewCurrent(adrs,lj^.dst);
	MakeNewCurrent(adrs,lj^.lim);
      END;
      expr^.elemByElem := current^.body^.loopJunk;
    END CreateLoopJunk;

  VAR
    actualType, formalType, acElTy : TypeDesc;
    compatible, ok : BOOLEAN;
    expand     : ExpandInfo;
    newChild   : ExprDesc;
    pVariable  : IdDesc;
    frameId    : IdDesc;
    ix         : CARDINAL;

  BEGIN
    actualType := actual^.exprType; (* neither of these can be *)
    formalType := formal^.type;     (* NIL  --  kjg  17-Nov-88 *)
    CASE formal^.form OF
      | valForm :
        CheckedAssignCompatible (actual, formalType, compatible);
	IF NOT (compatible OR
               UnivConform(actualType,formalType) OR
               UnivConform(WidenedType(actualType),formalType)) THEN 
	  Error (253);
	END;
        actual^.actualClass := valActual;
	IF  (formalType^.tyClass = arrays) AND
	    (actualType^.tyClass = S1) THEN
	  actual^.exprType := PointerTo(SS);
	END;
        (* no need to coerce S1s since these output as charLits *)
      | varForm :
        IF NOT IsVariable(actual) THEN Error (255); RETURN; END;
	(* Resolve any references to opaque types since elaborated *)
	IF actualType^.tyClass = opaqueTemp THEN
	  actualType := actualType^.resolvedType;
	END;
	IF formalType^.tyClass = opaqueTemp THEN	(* kjg 16-Jul-91 *)
	  formalType := formalType^.resolvedType;
	END;
        INCL(actual^.name.variable^.varUseSet,varParThr);
	IF AccessModeOf(actual^.name) IN anyUplevel THEN
	  INCL(actual^.name.variable^.varUseSet,uplevThr);
        END;
	(* The following IsFORThreat was originally made after the
	   compatibility check; it has been moved up and made a function to
	   bypass the compatibility check if a control variable is
	   threatened - otherwise, for constant FOR limits, the control
	   variable temporary type (see cvTmp below) could not match the
	   formal. This modification means that where a control variable is
	   threatened and the types do not match, only the threat error
	   message will be produced - till we get a better idea. *)
        IF IsFORThreat(actual^.name.variable) THEN 
	  Error(297); RETURN;
	END;
        IF (actualType <> formalType) AND
           NOT UnivConform (actualType, formalType) THEN
	  LoadGlobals(actualType,formalType);
	  Error (254); RETURN;
	END;
        actual^.actualClass := refActual;
	actual^.testFlags := noTests;
      | openValForm :
	IF actual^.exprType^.tyClass = stringTs THEN
	 (*
	  *  Check as for var param, fix with wrapper proc.
	  *)
	  needWr := TRUE;
          actual^.actualClass := VarOpenCompatible(actualType,formal);
	  IF (actual^.exprClass = desigNode) AND
	     (AccessModeOf(actual^.name) IN anyUplevel) THEN
	    INCL(actual^.name.variable^.varUseSet,uplevThr);
          END;
	  actual^.testFlags := actual^.testFlags * ixOnly;
	ELSE
         (*
	  *  First allocate the appropriate marshalling node
	  *)
          newChild := actual;
	  IF (newChild^.exprType^.tyClass = arrays) AND
	     (newChild^.exprType^.indexType = crdTyPtr) THEN
	   (*
	    *  Open marshalling nodes must be placed on the
	    *  global adjustment node sequence.
	    *)
	    CreateExprDesc(actual, openMarshallNode);
	    CreateExprDesc(actual^.mrshPtr, desigNode);
	    CreateIdDesc(anonBkt, pVariable, varNode);
	    actual^.mrshPtr^.name.variable := pVariable;

IF verbose IN modState THEN 
StdError.WriteString("marshalling of uplevel expression ");
StdError.WriteCard(newChild^.sourceLoc.line,1);
StdError.Write(":");
StdError.WriteCard(newChild^.sourceLoc.pos,1);
StdError.WriteString(" access modes=");
StdError.WriteCard(ORD(AccessModeOf(newChild^.name)), 1);
StdError.WriteCard(ORD(AccessModeOf(actual^.mrshPtr^.name)), 2);
StdError.WriteLn;
END;

	    IF AccessModeOf(newChild^.name) >= uplevel THEN
              ForceAccessMode(actual^.mrshPtr^.name, uplevel);
	      pVariable^.lexLev := newChild^.name.variable^.lexLev;
	      INCL(pVariable^.varUseSet, uplevAcc);
            ELSE 
	      ForceAccessMode(actual^.mrshPtr^.name, directLocl);
            END;

IF verbose IN modState THEN 
StdError.WriteString("post marshalling of expression ");
StdError.WriteCard(newChild^.sourceLoc.line,1);
StdError.Write(":");
StdError.WriteCard(newChild^.sourceLoc.pos,1);
StdError.WriteString(" access modes=");
StdError.WriteCard(ORD(AccessModeOf(newChild^.name)), 1);
StdError.WriteCard(ORD(AccessModeOf(actual^.mrshPtr^.name)), 2);
StdError.WriteLn;
END;

	    MakeTempName(pVariable);
           (*  previous code -- old code 
	    *    pVariable^.varType  := intTyPtr; 
            *)
	    pVariable^.varType  := adrTyPtr; 
	    pVariable^.varClass := auto;
	    frameId := newChild^.name.variable^.decFrame;
	   (*
	    *   We must mark this variable as being threatened: 
	    *   it cannot go in a regvar since the preamble code 
	    *   of the EXPAND can't tell which reg to use...
	    *)
	    INCL(pVariable^.varUseSet, varParThr);
	    NEW(expand);
	    expand^.mrshNode := actual;
	    IF ((formalType^.tyClass = words) OR
	        (formalType^.tyClass = bytes)) AND (formal^.dimN = 1) THEN
	     (*
	      *  If the formal is an open array of byte or word,
	      *  the marshalling area and dimensionality is 
	      *  determined by the _actual_ parameter.
	      *)
	      GetOpenInfo(newChild,expand^.dimenNum,expand^.elemType);
	    ELSE
	     (*
	      *  Otherwise the actual dimensionality is the 
	      *  same as the formal, and the element size is
	      *  determined by the _formal_ parameter size.
	      *)
	      expand^.dimenNum := formal^.dimN;
	      expand^.elemType := formalType;
	    END;
	    LinkRight(frameId^.body^.adjustSeq,expand);
	    InsertRef(frameId^.scope,pVariable,ok);
(*
 *	  StdError.WriteCard(actual^.sourceLoc.line,0);
 *	  StdError.WriteString(": Marshall open array ");
 *	  DiagName(newChild^.name.variable^.decFrame^.name);
 *	  StdError.Write(".");
 *	  DiagName(newChild^.name.variable^.name);
 *	  StdError.WriteString(": used in ");
 *	  DiagName(current^.name);
 *	  StdError.WriteLn;
 *)
	  ELSE
	   (*
	    *  For fixed marshalling nodes, the default 
	    *  dst size is the same as the source size
	    *)
	    CreateExprDesc(actual,fixedMarshallNode);
	    actual^.mrshSiz := actualType^.size;
	  END;
	  actual^.actualX := newChild;
	  actual^.elemByElem := NIL;
	  actual^.exprType   := formalType;
          actual^.actualClass := ValOpenCompatible(actualType, formal);
          IF actual^.actualClass = open1D THEN (* more checks *)
	    IF IsOrdinalType(formalType) THEN
	     (*
	      *  Find the real element type, even if multi-dim.
	      *)
	      acElTy := actualType;
	      FOR ix := 1 TO formal^.dimN DO acElTy := acElTy^.elementType END;
	     (*
	      *  Ordinal types might change size.
	      *  For the fixed case the size is computed here, 
	      *  for the open case it is computed at runtime.
	      *)
	      IF formalType^.size <> acElTy^.size THEN
	        CreateLoopJunk(actual);
	        IF actual^.exprClass = fixedMarshallNode THEN
	          actual^.mrshSiz :=
			(actualType^.size DIV acElTy^.size) * formalType^.size;
	        END;
	   (*
	    *   StdError.WriteCard(actual^.sourceLoc.line,0);
	    *   StdError.WriteString(": Open array changes size" + 12C);
	    *)
	      END;
	      IF TypesOverlap(formalType,acElTy) THEN
	        newChild^.testFlags := noTests;
	      ELSE
	        CreateLoopJunk(actual);
	   (*
	    *   StdError.WriteCard(actual^.sourceLoc.line,0);
	    *   StdError.WriteString(": Open array needs elemByElem check"+12C);
	    *)
	      END;
              IF newChild^.exprType = PointerTo(S1) THEN (* coerce to string *)
                newChild^.exprType := PointerTo(SS);
              END;
	      IF newChild^.exprType = PointerTo(SS) THEN
	        actual^.mrshSiz := newChild^.conValue.strHigh + 1;
	      END;
	    END;
          END;
        END;
      | openVarForm :
        IF NOT IsVariable(actual) THEN Error (255)
	(*  new code to handle varParThreat attribute *)
        ELSIF IsFORThreat(actual^.name.variable) THEN Error(297);
	ELSE
          actual^.actualClass := VarOpenCompatible(actualType,formal);
	  INCL(actual^.name.variable^.varUseSet,varParThr);
	  (* mark variable as being threatened *)
	  IF AccessModeOf(actual^.name) IN anyUplevel THEN
	    INCL(actual^.name.variable^.varUseSet,uplevThr);
          END;
	  actual^.testFlags := actual^.testFlags * ixOnly;
        END;
      ELSE Error (299) (* else of CASE *)
    END (* case *)
  END CheckActualParam;

PROCEDURE CheckDirectParamList (VAR actuals : Sequence (* of ExprDesc *);
                                    formals : Sequence (* of FormalType *) ); 
(* 
 *  Check actuals against formals, and copy FormalClass to actuals.
 *  Unlike CheckActualParamList, no high descriptors are formed
 *  for procedures tagged as "direct". These obey C conventions.
 *)

  VAR
    actualsCurs, formalsCurs : ElemPtr;
    argList : Sequence;
    actual  : ExprDesc;
    formal  : FormalType;
    junk    : BOOLEAN;

BEGIN (* CheckDirectParamList *)
  InitSequence(argList);
  InitCursor (actuals, actualsCurs);
  InitCursor (formals, formalsCurs);
  WHILE NOT Ended(actualsCurs) AND
        NOT Ended(formalsCurs) DO
    GetNext (actualsCurs, actual);
    GetNext (formalsCurs, formal);
    TraverseExp (actual);
    (*
     *  being here ==> no synErrors ==> actual <> NIL; but after
     *  semErrors, actual^.exprType = NIL, so to protect code ...
     *)
    IF actual^.exprType <> NIL THEN (* kjg 17-Nov-88 *)
      CheckActualParam (junk, actual, formal);
      LinkRight(argList,actual);
    END; (* of if exprType<>NIL *)
  END; (* of while NOT Ended(actualCurs) AND NOT Ended(formalCurs) *)
  (*
   * at least one of the Ended predicates is true, so ...
   *)
  IF    NOT Ended(formalsCurs) THEN Error (248); 
  ELSIF NOT Ended(actualsCurs) THEN Error216(actualsCurs);
  END;
  DisposeList(actuals); actuals := argList;
END CheckDirectParamList;

(* ---------------------------------------------------- *) 

PROCEDURE CheckActualParamList (VAR needWr  : BOOLEAN;
				VAR actuals : Sequence (* of ExprDesc *);
                                    formals : Sequence (* of FormalType *) ); 
(* --------------------------------------- *
 *  Check actuals against formals, and copy FormalClass to actuals.
 *  Also, if necessary add a high value descriptor to the param list
 * --------------------------------------- *)

  PROCEDURE CreateArrayHighN(dim : CARDINAL;	(* dim of high needed *)
			     ack : ExprDesc;    (* actual param expr. *)
		         VAR hiD : ExprDesc);	(* result high expr.  *)
    VAR arrayTyp : TypeDesc;
	highDesc : IdDesc;
	ix       : CARDINAL;
  BEGIN
    IF  (ack^.exprClass = openMarshallNode) OR
	(ack^.exprClass = fixedMarshallNode) THEN ack := ack^.actualX END;
    arrayTyp := ack^.exprType; ix := dim;
    FOR ix := 1 TO dim-1 DO arrayTyp := arrayTyp^.elementType END;
    IF ack^.exprType^.tyClass = SS THEN
      CreateExprDesc(hiD,literalNode);
      hiD^.conValue.fixValue := ack^.conValue.strHigh;
    ELSIF NOT arrayTyp^.isDynamic THEN
      CreateExprDesc(hiD,literalNode);				(*$T-*)
      hiD^.conValue.fixValue := IndexCardinality(arrayTyp) - 1;	(*$T=*)
    ELSE (* IF arrayTyp^.isDynamic THEN *)
      CreateExprDesc(hiD,desigNode);
      highDesc := ack^.name.variable^.nextHigh;
      FOR ix := 1 TO dim-1 DO highDesc := highDesc^.nextHigh END;
      hiD^.name.variable := highDesc;
     (* 
      *  now check for that pesky uplevel possibility: 
      *  actual.name is uplevel or uplevel indirect
      *)
      IF AccessModeOf(ack^.name) >= uplevel THEN
	ForceAccessMode(hiD^.name,uplevel);
      ELSE 
	ForceAccessMode(hiD^.name,highAccess);
      END;
    END;
    hiD^.exprType := crdTyPtr;
  END CreateArrayHighN;

 (* --------------------------------------- *)

  PROCEDURE CreateByteHigh(ack : ExprDesc;
		       VAR hiD : ExprDesc);

    PROCEDURE MakeLit(v : INTEGER) : ExprDesc;
      VAR e : ExprDesc;
    BEGIN
      CreateExprDesc(e, literalNode);
      e^.testFlags := noTests;
      e^.exprType  := crdTyPtr;
      e^.conValue.intValue := v;
      RETURN e;
    END MakeLit;

    PROCEDURE MakeMul(l,r : ExprDesc) : ExprDesc;
      VAR e : ExprDesc;
    BEGIN
      CreateExprDesc(e, starNode);
      e^.testFlags := noTests;
      e^.exprType  := crdTyPtr;
      e^.leftOp := l; e^.rightOp := r;
      RETURN e;
    END MakeMul;

    PROCEDURE MakeAdd(l,r : ExprDesc) : ExprDesc;
      VAR e : ExprDesc;
    BEGIN
      CreateExprDesc(e, plusNode);
      e^.testFlags := noTests;
      e^.exprType  := crdTyPtr;
      e^.leftOp := l; e^.rightOp := r;
      RETURN e;
    END MakeAdd;

    VAR ackTyp : TypeDesc;
	elmTyp : TypeDesc;
	origHi : ExprDesc;
	opnDim : CARDINAL;
	elmSiz : CARDINAL;
	index  : CARDINAL;
  BEGIN
    IF  (ack^.exprClass = openMarshallNode) OR
	(ack^.exprClass = fixedMarshallNode) THEN ack := ack^.actualX END;
    ackTyp := ack^.exprType;
    IF ackTyp^.tyClass = SS THEN
      hiD := MakeLit(ack^.conValue.strHigh);
    ELSIF ackTyp^.tyClass = arrays THEN
      GetOpenInfo(ack,opnDim,elmTyp);
      elmSiz := elmTyp^.size;
     (*
      *  Treat this as an ordinary 1D array, then scale...
      *)
      IF opnDim = 0 THEN 
	hiD := MakeLit(elmSiz - 1);
      ELSIF opnDim = 1 THEN 
       (* 
	*  An algebraic rearrangement :
	*
	* (actual HIGH + 1) * sizeMultiple - 1 =>
	*	(actual HIGH * sizeMultiple) + (sizemultiple-1) 
	*)
	CreateArrayHighN(1,ack,origHi);
	hiD := MakeAdd( MakeMul(origHi,MakeLit(elmTyp^.size)),
			MakeLit(elmTyp^.size - 1));
      ELSE
       (*
	*  Must do this the hard way!
	*)
	hiD := MakeLit(elmSiz);
	FOR index := 1 TO opnDim DO
	  CreateArrayHighN(index,ack,origHi);
	  hiD := MakeMul(hiD,MakeAdd(origHi,MakeLit(1)));
	END;
	hiD := MakeAdd(hiD,MakeLit(-1));
      END;
    ELSE (* some ordinary known-size  expression *)
      hiD := MakeLit(ackTyp^.size - 1);
    END;
  END CreateByteHigh;

 (* --------------------------------------- *)

  PROCEDURE CreateWordHigh(ack : ExprDesc;
		       VAR hiD : ExprDesc);
    VAR divExpr : ExprDesc;
  BEGIN
    CreateByteHigh(ack,hiD);
    IF hiD^.exprClass = literalNode THEN
      hiD^.conValue.fixValue := hiD^.conValue.fixValue DIV wordSize;
    ELSE
      CreateExprDesc(divExpr,divNode);
      WITH divExpr^ DO
	testFlags := noTests;
	exprType := crdTyPtr;
	leftOp := hiD;
	CreateExprDesc(rightOp,literalNode);
	WITH rightOp^ DO
	  testFlags := noTests;
	  exprType := crdTyPtr;
	  conValue.fixValue := wordSize;
        END;
      END;
      hiD := divExpr;
    END;
  END CreateWordHigh;

 (* --------------------------------------- *)

  VAR
    actualsCurs, formalsCurs : ElemPtr;
    actual : ExprDesc;
    formal : FormalType;
    argList : Sequence; (* the replacement arg list  *)
    size    : CARDINAL; (* cardinality of open array *)
    dimIx   : CARDINAL;
    highExp : ExprDesc; (* created HIGH expression   *)
    formalSize, actualSize, sizeMultiple : CARDINAL; (* open HIGH sizes *)
    multiply : ExprDesc; (* used in constructing open HIGH expression *)

BEGIN (* CheckActualParamList *)
  InitSequence(argList);
  InitCursor (actuals, actualsCurs);
  InitCursor (formals, formalsCurs);
  WHILE NOT Ended(actualsCurs) AND
        NOT Ended(formalsCurs) DO
    GetNext (actualsCurs, actual);
    GetNext (formalsCurs, formal);
    TraverseExp (actual);
    (*
     *  being here ==> no synErrors ==> actual <> NIL; but after
     *  semErrors, actual^.exprType = NIL, so to protect code ...
     *)
    IF actual^.exprType <> NIL THEN (* kjg 17-Nov-88 *)
      CheckActualParam (needWr, actual, formal);
      (* now build the arg list *)
      LinkRight(argList,actual);
      IF actual^.actualClass >= open1D THEN
       (*
	*  Create high descriptor(s) for an open array
	*  each descriptor is added to the argument list
	*)
	IF actual^.exprType^.tyClass = stringTs THEN
	  CreateExprDesc(highExp,errNode);
	  highExp^.exprType := intTyPtr;
          LinkRight(argList,highExp);
        ELSIF actual^.actualClass = byteOpen THEN
	  CreateByteHigh(actual,highExp);
          LinkRight(argList,highExp);
        ELSIF actual^.actualClass = wordOpen THEN
	  CreateWordHigh(actual,highExp);
          LinkRight(argList,highExp);
        ELSE (* IF actual^.actualClass = open1D THEN *)
	  FOR dimIx := 1 TO formal^.dimN DO
	    CreateArrayHighN(dimIx,actual,highExp);
            LinkRight(argList,highExp);
	  END;
	END;
      END; (* else do nothing, end of open processing *)
    END; (* of if exprType<>NIL *)
  END; (* of while NOT Ended(actualCurs) AND NOT Ended(formalCurs) *)
  (*
   *  at least one of the Ended predicates is true, so ...
   *)
  IF    NOT Ended(formalsCurs) THEN Error (248); (* pos'n = pos'n of the *)
                                                 (* last expr traversed  *)
  ELSIF NOT Ended(actualsCurs) THEN Error216(actualsCurs);
  END;
  DisposeList(actuals); actuals := argList;
END CheckActualParamList;

(*================================================================*)

  VAR  currentWith : WithDesc;

  PROCEDURE WithBinding(hash : HashBucketType) : IdDesc;
    VAR withPtr   : WithDesc;
        idp       : IdDesc;
  BEGIN
    idp := NIL;
    withPtr := currentWith;
    WHILE (idp = NIL) AND (withPtr <> NIL) DO
      IF withPtr^.dummy <> NIL THEN
        LookupInThisScope(withPtr^.dummy^.varType^.fields,hash,idp);
      END;
      withPtr := withPtr^.uphill;
    END;
    RETURN idp;
  END WithBinding;
 
  PROCEDURE ExceptVarThreat(id : IdDesc);
 (* Force to memory all variables referred to in both normal and except parts *)
  BEGIN
    IF id <> NIL THEN
      IF id^.idClass = varNode THEN
        IF     exceptState = inNormal THEN id^.normalRef := TRUE
        ELSIF (exceptState = inExcept) AND id^.normalRef THEN 
	  INCL(id^.varUseSet,varParThr);
	END;
      END;
    END;
  END ExceptVarThreat;


  PROCEDURE BindDesignator(VAR des : DesigRec);
    VAR idp : IdDesc;
        dst : DStateType;
        val : SelectAttribute;
        qualScope : IdTree;
        withPtr   : WithDesc;
	moreDesignator : BOOLEAN;	(* 15-Apr-92 *)
  BEGIN
    IF des.variable <> NIL THEN RETURN END; (* ==> supposed to be not bound *)
    InitDState(des,dst);
    GetSelector(dst,val); (* assert: first is identifierNode *)
    withPtr := currentWith;
    WHILE withPtr <> NIL DO
      IF withPtr^.dummy <> NIL THEN
        qualScope := withPtr^.dummy^.varType^.fields;
        LookupInThisScope(qualScope,val.hsh,idp);
        IF idp <> NIL THEN (* found ! *)
          des.variable := withPtr^.dummy; (* selectors are NOT moved *)
          IF des.variable = withPtr^.desig.variable THEN
            ForceAccessMode(des,AccessModeOf(withPtr^.desig));
          ELSE (* the local with pointer is used *)
            ForceAccessMode(des,indirect);
          END;
	  ExceptVarThreat(des.variable);
          RETURN;
        END;
      END;
      withPtr := withPtr^.uphill;
    END;
    (* RETURN not taken ==> ordinary lookup *)
    Lookup(val.hsh,idp); (* using current scope *)
    (* 15-Apr-92: avoid error 204 if designator ends with mod name *)
    moreDesignator := TRUE;
    WHILE (idp <> NIL) AND moreDesignator AND
          ((idp^.idClass = exportNode) OR (idp^.idClass = modNode)) DO
      qualScope := idp^.scope;
      GetSelector(dst,val);
      IF val.tag = identifierNode THEN
        LookupInThisScope(qualScope,val.hsh,idp);
      ELSIF val.tag = endMarker THEN moreDesignator := FALSE;
      ELSE idp := NIL;
      END;
    END; (* now at end of qualification part *)
    des.variable := idp; (* NIL if not found *)
    MoveSelectors(des,dst);
    (* now set access mode for variables *)
    IF idp <> NIL THEN
      IF idp^.idClass = varNode THEN
        (* determine mode of designator.variable *)
        SetAccessMode(des);
      ELSIF idp^.idClass = conProc THEN
        des.variable := idp^.procId;
      END;
    END;
    ExceptVarThreat(des.variable);
  END BindDesignator;


  PROCEDURE GetConstDesigVal(des : DesigRec;
			 VAR cTp : TypeDesc;
		         VAR cVl : LexAttType;
			 VAR isC : BOOLEAN);
  (*
   *	This procedure extracts the type and value of 
   *	constant designators possibly with selectors.
   *)
    VAR id  : IdDesc;
        stt : DStateType;
        sel : SelectNodeClass;
        val : SelectAttribute;
	offset : CARDINAL;
	conPtr : ConBlock;
	con, iVal : LexAttType;
	typ, iTyp : TypeDesc;
	comOK, isConst : BOOLEAN;
  BEGIN (* assert : expr.exprClass = desigNode *)
    typ := des.variable^.conType;
    con := des.variable^.conValue;
    InitDState(des,stt);
    isConst := TRUE; 
    LOOP
        GetSelector(stt,val);
        CASE val.tag OF
        | endMarker : EXIT;
        | dereferenceNode : Error(242); typ := NIL; EXIT;
        | subscriptNode :
            IF typ^.tyClass = arrays THEN
              TraverseExp(val.exp);
	      CheckedAssignCompatible(val.exp,typ^.indexType,comOK);
	      IF comOK THEN 
		iTyp := typ^.indexType;
                typ  := typ^.elementType;
		IF isConst AND (val.exp^.exprClass = literalNode) THEN

		  conPtr := con.adrsValue;
		  iVal   := val.exp^.conValue;
		  offset := OrdinalValue(iTyp,iVal) - MinOfOrdType(iTyp);
		  offset := offset * typ^.size;
		  ExtractCon(con,typ,ADR(conPtr^[offset]));

		ELSE 
		  isConst := FALSE;
		  val.exp^.exprType := iTyp;
		  (*
		   *   the previous assignment marks the 
		   *   expression type so that bounds checks
		   *   have a conveniently available type desc.
		   *   However, the type of the expression (in
		   *   the case of designators) must be re-evaluated
		   *   in order to allow fetch size determination
		   *)
		END;
              ELSE Error(207); typ := NIL; EXIT;
	      END;
            ELSE Error(237); typ := NIL; EXIT;
            END;
        | identifierNode :
            IF typ^.tyClass = records THEN
              LookupInThisScope(typ^.fields,val.hsh,id);
              IF (id <> NIL) AND (id^.idClass = fieldNode) THEN
                typ := id^.fieldType;
		conPtr := con.adrsValue;
		BindFieldName(des,stt,id); (* change tag *)
		IF isConst THEN 
		  ExtractCon(con,typ,ADR(conPtr^[id^.fieldOffset]));
		END;
              ELSE ErrIdent(233,val.hsh); typ := NIL; EXIT;
              END;
            ELSE Error(234); typ := NIL; EXIT;
            END;
        END; (* case *)
      END; (* loop *)
      isC := isConst;
      cTp := typ;
      IF isConst THEN cVl := con END;
  END GetConstDesigVal;

  PROCEDURE GetTypeAndValue(VAR expr : ExprRec);
  (*
   *	This procedure extracts the type and value of 
   *	constant designators possibly with selectors.
   *)
    VAR cVl : LexAttType;
	isC : BOOLEAN;
	typ : TypeDesc;
  BEGIN (* assert : expr.exprClass = desigNode *)
    GetConstDesigVal(expr.name,typ,cVl,isC);
    IF isC THEN
      expr.exprType := typ;
      expr.conValue := cVl; 
      expr.exprClass := literalNode;
      IF (typ = fltTyPtr) OR 
	   (typ = dblTyPtr) THEN expr.exprType := rrTyPtr END;
    ELSE 
     (* 
      *  this is not entirely constant, so don't change
      *	   the designator, but tag the ExprRec as a selConst
      *)
      expr.exprType  := typ;
      expr.exprClass := selConstNode;
    END;
  END GetTypeAndValue;

  PROCEDURE GetConstDesig(VAR des : DesigRec;
			  VAR typ : TypeDesc);
    VAR cVl : LexAttType;
	isC : BOOLEAN;
  BEGIN
    GetConstDesigVal(des,typ,cVl,isC);
    IF isC AND ((typ^.tyClass = procTypes) OR 
		(typ^.tyClass = funcTypes)) THEN
      des.variable := cVl.adrsValue;
    END;
  END GetConstDesig;

  PROCEDURE GetDesigType(des : DesigRec;
                     VAR typ : TypeDesc);
    VAR id  : IdDesc;
        stt : DStateType;
        sel : SelectNodeClass;
        val : SelectAttribute;
	comOK, forceIxTst : BOOLEAN;
  BEGIN
    IF (des.variable = NIL) OR
       ((des.variable^.idClass <> varNode) AND
        (des.variable^.idClass <> constNode)) THEN	(* kjg Nov 92 *)
      Error(235); typ := NIL;
    ELSE
      typ := des.variable^.varType;
      InitDState(des,stt);
      LOOP
	(*
	   must treat possible opaques
	*)
	IF typ^.tyClass = opaqueTemp THEN
          Assert(typ^.resolvedType <> NIL);
	  typ := typ^.resolvedType;
        END;
        GetSelector(stt,val);
        CASE val.tag OF
        | endMarker : EXIT;
        | dereferenceNode :
            IF typ^.tyClass = pointers THEN
              typ := typ^.targetType;
	    ELSIF typ^.tyClass =adrs THEN
	      typ := PointerTo(bytes);
            ELSE Error(236); typ := NIL; EXIT;
            END;
        | subscriptNode : 
            TraverseExp(val.exp);
            forceIxTst := (indexTests IN val.exp^.testFlags);
            IF typ^.tyClass = arrays THEN
             (*
              * Note that CheckedAssignCompatible will erroneously decide
              * that all index expressions of wholly positive type are
              * contained within the range of any open array index type.
              * It will therefore clear the indexTests flag. Boolean
              * forceIxTst notes this case, and restores the flag.
              *)
              forceIxTst := forceIxTst AND
                                typ^.isDynamic AND
                                ((val.exp^.exprClass <> literalNode) OR
                                 (val.exp^.conValue.fixValue <> 0));
              CheckedAssignCompatible(val.exp,typ^.indexType,comOK);
             (*
              *   the previous assignment marks the
              *   expression type so that bounds checks
              *   have a conveniently available type desc.
              *   However, the type of the expression (in
              *   the case of designators) must be re-evaluated
              *   in order to allow fetch size determination
              *)
              typ := typ^.elementType;
            ELSIF typ^.tyClass = stringTs THEN
              CheckedAssignCompatible(val.exp,intTyPtr,comOK);
              INCL(val.exp^.testFlags,isStrIx);
              typ := typ^.targetType;
            ELSE Error(237); typ := NIL; EXIT;
            END;
            IF NOT comOK THEN Error(207) END;
            IF forceIxTst THEN INCL(val.exp^.testFlags,indexTests) END;
        | identifierNode :
            IF typ^.tyClass = records THEN
              LookupInThisScope(typ^.fields,val.hsh,id);
              IF (id <> NIL) AND (id^.idClass = fieldNode) THEN
                typ := id^.fieldType;
                BindFieldName(des,stt,id); (* change tag *)
              ELSE ErrIdent(233,val.hsh); typ := NIL; EXIT;
              END;
            ELSE Error(234); typ := NIL; EXIT;
            END;
        END; (* case *)
      END; (* loop *)
    END; (* else *)
  END GetDesigType;

  PROCEDURE EnterWith(VAR with : WithDesc);
    VAR ptr : TypeDesc; id : IdDesc;
  BEGIN
    WITH with^ DO
      IF  (desig.variable = NIL) OR
          (desig.variable^.idClass <> varNode) THEN
        Error(235); dummy := NIL;
      ELSIF EmptySelList(desig) AND
	    (desig.variable^.varClass <= extern) AND (* improved code Oct 90 *)
	    (desig.variable^.varClass <> auto) THEN
	(*
	 *  fields of entire static vars are directly
	 *  addressed, others have adr placed in reg.
	 *)
        dummy := desig.variable; (* variable is entire *)
	IF dummy^.varType^.tyClass <> records THEN
	  Error(232); dummy := NIL;
	END;
      ELSE (* scan remaining selectors *)
        GetDesigType(desig,ptr);
        IF ptr = NIL THEN dummy := NIL;
        ELSIF ptr^.tyClass <> records THEN
          Error(232); dummy := NIL;
        ELSE
          CreateIdDesc(anonBkt,id,varNode);
(*
 *        MakeWithName(id); (* invent unique name (for C-boostrap version) *)
 *)
          id^.varType := ptr;
          id^.varClass := auto;
          dummy := id;
        END;
      END; (* else *)
    END;
    with^.uphill := currentWith; currentWith := with;
  END EnterWith;

  PROCEDURE ExitWith();
  BEGIN
    currentWith :=  currentWith^.uphill;
  END ExitWith;

(*==============================================================*
 *
 *  PROCEDURE Align(VAR off : INTEGER;
 *			alg : CHAR);
 *    VAR mask : INTEGER;
 *  BEGIN
 *    mask := ORD(alg);
 *    off  := CAST(CARDINAL,
 *		   CAST(BITSET,(off + mask)) - CAST(BITSET,mask));
 *  END Align;
 *
 *  PROCEDURE NeedsDestPtr(ty : TypeDesc) : BOOLEAN;
 *  BEGIN
 *    WITH ty^ DO
 *      RETURN ((result <> NIL) AND
 *		((result^.tyClass = records) OR
 *		 (result^.tyClass = arrays)  OR
 *		 ((result^.tyClass = sets) AND
 *		  (result^.size > 4))));
 *    END;
 *  END NeedsDestPtr;
 *
 *  PROCEDURE IsArray(ty : TypeDesc) : BOOLEAN;
 *  BEGIN
 *    RETURN (ty^.tyClass = arrays) OR
 *	     (ty^.tyClass = sets) AND (ty^.size > 4);
 *  END IsArray;
 *
 *==============================================================*)

  PROCEDURE RecordCallOf(id : IdDesc);   (* by "current" *)
    (* Constructs the adjacency lists for the "calls"    *)
    (* graph. Only calls of internal procs are entered,  *)
    (* those that call imported procs are merely tagged. *)

  BEGIN
(*
 *	DiagName(current^.name);
 *	StdError.WriteCard(current^.body^.maxParSize,4);
 *	StdError.WriteString(" calls ");
 *	DiagName(id^.name);
 *)
    CASE id^.idClass OF
    | procNode, procHeader :
	IF id^.procType^.parSiz = infinity THEN
	  id^.procType^.parSiz := FormalSize(id^.procType);
	END;
(*
 *	StdError.WriteCard(id^.procType^.parSiz,4);
 *)
	IF id^.procType^.parSiz > current^.body^.maxParSize THEN
	  current^.body^.maxParSize := id^.procType^.parSiz;
	END;
    | modNode : (* skip *)
    | externProc :
	IF id^.procType^.parSiz = infinity THEN
	  id^.procType^.parSiz := FormalSize(id^.procType);
	END;
(*
 *	StdError.WriteCard(id^.procType^.parSiz,4);
 *)
	IF id^.procType^.parSiz > current^.body^.maxParSize THEN
	  current^.body^.maxParSize := id^.procType^.parSiz;
	END;
    | varNode : (* this is after qualidents are resolved *)
	IF id^.varType^.parSiz = infinity THEN
	  id^.varType^.parSiz := FormalSize(id^.varType);
	END;
	IF id^.varType^.parSiz > current^.body^.maxParSize THEN
	  current^.body^.maxParSize := id^.varType^.parSiz;
	END;
    ELSE (* stProc, stFunc, typeNode : *) (* nothing *)
    END;
(*
 *	StdError.WriteLn;
 *	StdError.WriteString("new maxParSize ");
 *	StdError.WriteCard(current^.body^.maxParSize,4);
 *	StdError.WriteLn;
 *)
  END RecordCallOf;

  PROCEDURE CheckDesignator(exp : ExprDesc;
                        VAR idp : IdDesc);
    (* check exp-node is a designator, return ptr *)
  BEGIN (* assert: exp already traversed ==> unknown
           ids have already signalled Error(204)  *)
    IF exp^.exprClass <> desigNode THEN
      Error(214); idp := NIL;
    ELSE idp := exp^.name.variable;
    END;
  END CheckDesignator;

  PROCEDURE CheckTypeId(exp : ExprDesc;
                    VAR tdp : TypeDesc);
    (* exp is a node designating a type id else return NIL *)
    VAR idp : IdDesc;
  BEGIN
    lastPos := exp^.sourceLoc; tdp := NIL;
    IF exp^.exprClass = desigNode THEN
      BindDesignator(exp^.name);
      idp := exp^.name.variable;
      IF idp = NIL THEN Error(204); (* unknown *)
      ELSIF idp^.idClass <> typeNode THEN Error(205);
      ELSIF NOT EmptySelList(exp^.name) THEN Error(286);
      ELSE tdp := idp^.typType;
      END;
    ELSE Error(214);
    END;
  END CheckTypeId;

  PROCEDURE CheckTypeOfDesig(exp : ExprDesc;
			 VAR typ : TypeDesc);
    VAR idp : IdDesc;
  BEGIN
    lastPos := exp^.sourceLoc; typ := NIL;
    IF exp^.exprClass = desigNode THEN
      BindDesignator(exp^.name);
      idp := exp^.name.variable;
      IF idp = NIL THEN Error(204); (* unknown *)
      ELSIF idp^.idClass = varNode THEN
        GetDesigType(exp^.name,typ);
(*
 *   now use ptr^.size for size (kjg 25-May-89)
 *
 *(*
 *   this kludge changes the actual param to be a type designator
 *   irrespective of whether it _was_ a variable or type name 
 **)
 *        CreateIdDesc(anonBkt,idp,typeNode);
 *        idp^.typType := typ;
 *        exp^.name.variable := idp;
 *(*
 *   of course this may leave the select list in an invalid
 *   state in the case that there are selectors on a varNode;
 *   however we assert that only the typType field is used
 **)
 *  end of delete of 25-May-89
 *)
      ELSIF idp^.idClass = typeNode THEN 
	typ := idp^.typType;
	IF NOT EmptySelList(exp^.name) THEN Error(286) END;
      ELSE Error(205);
      END;
    ELSE Error(214);
    END;
  END CheckTypeOfDesig;

  PROCEDURE GetTyClass(exp : ExprDesc) : TyNodeClass;
  (*
   *  Return the (host) type class.
   *)
  BEGIN
    WITH exp^.exprType^ DO
      IF tyClass = subranges THEN
        RETURN (hostType^.tyClass);
      ELSE RETURN (tyClass);
      END;
    END;
  END GetTyClass;

  PROCEDURE WidenedType(ty : TypeDesc) : TypeDesc;
  BEGIN
    IF (ty <> NIL) AND (ty^.tyClass = subranges) THEN
      RETURN ty^.hostType;
    ELSE RETURN ty;
    END;
  END WidenedType;

  PROCEDURE TraversePrecon(t : TypeDesc);

    (****************************************************)
    PROCEDURE ParIndex(i : IdDesc) : CARDINAL;
      VAR curs : ElemPtr;
	  parm : FormalType;
	  ordn : CARDINAL;
    BEGIN
      (* find the index of the parameter i *)
      ordn := 0;
      InitCursor(t^.params,curs); 	(* uplevel access! *)
      WHILE NOT Ended(curs) DO
	GetNext(curs,parm); INC(ordn);
	IF parm^.fNam = i^.name THEN RETURN ordn END;
	IF parm^.dimN <> 0 THEN INC(ordn,parm^.dimN) END;
      END;
    END ParIndex;
    (****************************************************)

    PROCEDURE BindPosPars(exp : ExprDesc);
      VAR class : ExprNodeClass;
	  param : ExprDesc;
	  curs  : ElemPtr;
	  posId : IdDesc;
	  range : RangeDesc;
    BEGIN
      IF exp = NIL THEN RETURN END;
      class := exp^.exprClass;
      CASE class OF
      | literalNode : (* skip *)
      | desigNode :
	  IF (exp^.name.variable <> NIL) AND
	     (exp^.name.variable^.varClass >= valForm) THEN
	    CreateIdDesc(anonBkt,posId,posParNode); 
	    posId^.posIndex := 
		ParIndex(exp^.name.variable) + exp^.name.variable^.hiDepth;
	    exp^.name.variable := posId;
	  END;
      | funcDesigNode :
	 (* function designator does not need checking *)
	  InitCursor(exp^.paramSeq,curs);
	  WHILE NOT Ended(curs) DO
	    GetNext(curs,param);
	    BindPosPars(param);
	  END;
      | setDesigNode, constructorNode : (* recurse on elements *)
	  InitCursor(exp^.rangeSeq,curs);
	  WHILE NOT Ended(curs) DO
	    GetNext(curs,range);
	    BindPosPars(range^.lower);
	    IF range^.upper <> NIL THEN
	      BindPosPars(range^.upper);
	    END;
	  END;
      ELSE
	Assert(class <= negateNode, "bad expr class in BindPosPars");
	BindPosPars(exp^.leftOp);
	IF class <= inNode THEN BindPosPars(exp^.rightOp) END;
      END; (* case *)
    END BindPosPars;

    VAR proxy : ExprDesc;

  BEGIN
    proxy := t^.preCon;
    TraverseExp(proxy);
    IF NOT Compatible(proxy^.exprType,PointerTo(bools)) THEN
      Error(221);
      t^.preCon := NIL;
    ELSE (* all ok *)
      BindPosPars(proxy);
      t^.preCon := CAST(ADDRESS,proxy);
    END;
  END TraversePrecon;

  PROCEDURE TraverseExp(VAR exp : ExprDesc);
    (* recursively traverse exp tree, binding ids *)
    (* postcondition : type is determined (or NIL), all unknown
                       desigs or wrong classes have been flagged *)

    VAR id   : IdDesc;  ty   : TypeDesc;
        curs : ElemPtr; parX : ExprDesc;
	oldName : DesigRec;
        class, leftClass : TyNodeClass;
	dummy : BOOLEAN;
	wrap  : BOOLEAN;
	origExp : ExprDesc;


    PROCEDURE MakeCast(VAR res : ExprRec;	(* result *)
                           typ : TypeDesc;	(* target *)
                           exp : ExprDesc);	(* child  *)
     (* ========== cast fixup '95 ========== *)
      VAR newI : IdDesc;
	  newX : ExprDesc;
	  ok   : BOOLEAN;
	  dCls : TyNodeClass;
	  sCls : TyNodeClass;
     (* ===================================== *)
    BEGIN
     (* ========== cast fixup '95 ========== *)
      CreateExprDesc(newX,castNode);
      newX^.exprType := typ;
      newX^.source   := exp;
      newX^.wrd2wrd  := FALSE;
     (* ===================================== *)
      TraverseExp(exp);
      IF (typ <> NIL) AND (exp^.exprType <> NIL) THEN
        dCls := typ^.tyClass;
        sCls := exp^.exprType^.tyClass;
	IF (sCls = arrays) AND exp^.exprType^.isDynamic THEN Error(319) END;
       (*
	*  First case:
	*  word sized or less stuff which fits in an iReg
	*  In this case we demand a temporary, but do not
	*  insist that it be allocated to memory...
	*
	*  Here we also filter out the trivial case.
	*)
        IF (typ <> exp^.exprType) AND
	   (typ^.size <= wordSize) AND
	     NOT (dCls IN 
		TyClassSet{records,arrays,floats,doubles,hInts}) AND
	     NOT (sCls IN 
		TyClassSet{records,arrays,floats,doubles,hInts,RR,SS}) THEN
	  CreateIdDesc(anonBkt,newI,varNode);
	  MakeTempName(newI);
          newX^.needTmp  := TRUE;
          newX^.wrd2wrd  := TRUE;
	  newX^.tempId   := newI;
          (* commented out for type casting purposes *)
	  (*
	   * IF (exp^.exprClass = literalNode) AND
           * 	NOT HasAddress(exp) THEN Error(291) END;
	   *)
	  newI^.varType  := crdTyPtr; (* any old word-sized thing *)
	  newI^.varClass := auto;
	  EXCL(exp^.testFlags,rangeTests);
       (*
	*  Second case:
	*  expression must have an address in memory.
	*  In this case we demand a temporary, _and_
	*  insist that it be allocated to memory...
	*  we can ensure this by making it type array.
	*)
        ELSIF HasAddress(exp) OR 
		(exp^.exprClass <> literalNode) THEN
         (*
	  *  If alignment of destination is _more_ stringent than
	  *  the source, or if the source expression is a real value,
	  *  or if the destination is a real, or the expression does
	  *  not have an address then we must use a temp.
	  *)
          newX^.needTmp := 
		(typ^.alignMask > exp^.exprType^.alignMask) OR
		(sCls IN TyClassSet{floats,doubles,hInts}) OR
		(dCls IN TyClassSet{floats,doubles,hInts}) OR
		NOT HasAddress(exp);
	  IF newX^.needTmp THEN 
	    CreateIdDesc(anonBkt, newI, varNode);
	    MakeTempName(newI);
	    newI^.varClass := auto;
	    newX^.tempId   := newI;
	    CreateTypeDesc(thisCompileUnit, newI^.varType, arrays);
	    WITH newI^.varType^ DO
	      IF exp^.exprType^.size > typ^.size THEN 
	        size := exp^.exprType^.size;
	      ELSE
	        size := typ^.size;
	      END;
	      IF exp^.exprType^.alignMask > typ^.alignMask THEN 
	        alignMask := exp^.exprType^.alignMask;
	      ELSE
	        alignMask := typ^.alignMask;
	      END;
	    END;
	  END;
       (*
	*  All other cases are literals, and are erroneous
	*)
        ELSE (* exp^.exprClass = literalNode *) Error(291);
	END;
      END;
      IF newX^.needTmp THEN InsertRef(current^.scope, newI, ok) END;
      res := newX^; (* overwrite node! *)
     (* ===================================== *)
    END MakeCast;

    PROCEDURE StFuncCheck(sel : StandardProcs;
                      VAR exp : ExprRec);

      PROCEDURE Wg13ValRules(dst,exp : TypeDesc) : BOOLEAN;
      BEGIN
	IF (dst = NIL) OR (exp = NIL) THEN RETURN TRUE END;
	IF dst^.tyClass = subranges THEN dst := dst^.hostType END;
	IF exp^.tyClass = subranges THEN exp := exp^.hostType END;
        RETURN
	  (dst = exp) OR
	  (dst^.tyClass IN iNumVar) OR (* non-lit whole number classes *)
	  (exp^.tyClass IN iNumVal) OR (* add in the literal classes   *)
	  ((dst^.tyClass IN numeric - litSets) AND (exp^.tyClass IN numeric));
(*
 *	  ((dst^.tyClass IN wg13Num - litSets) AND (exp^.tyClass IN wg13Num));
 *)
      END Wg13ValRules;

      PROCEDURE GetHighDescriptor(name : DesigRec; VAR high : IdDesc);
        VAR idp : IdDesc;
            dst : DStateType;
            val : SelectAttribute;
      BEGIN
	InitDState(name,dst);
	GetSelector(dst,val); (* assert: first is identifierNode *)
	high := name.variable^.nextHigh;
        WHILE (high <> NIL) AND (val.tag = subscriptNode) DO
	  high := high^.nextHigh;
	  GetSelector(dst,val);
	END;
        IF val.tag <> endMarker THEN high := NIL END;
      END GetHighDescriptor;

(* -------- For bootstrapping --------- *
      VAR   dblwrd : RECORD CASE : INTEGER OF
			| 0 : dbl   : REAL;
			| 1 : flt   : SHORTREAL;
			| 2 : lo,hi : Card32;
		     END; END;
      PROCEDURE MinReal() : REAL;
      BEGIN
	  IF bigEndian THEN
	    dblwrd.lo := 0FFEFFFFFH;
	    dblwrd.hi := 0FFFFFFFFH;
	  ELSE
	    dblwrd.lo := 0FFFFFFFFH;
	    dblwrd.hi := 0FFEFFFFFH;
	  END;
          RETURN dblwrd.dbl;
      END MinReal;

      PROCEDURE MaxReal() : REAL;
      BEGIN
	  IF bigEndian THEN
	    dblwrd.lo := 07FEFFFFFH;
	    dblwrd.hi := 0FFFFFFFFH;
	  ELSE
	    dblwrd.lo := 0FFFFFFFFH;
	    dblwrd.hi := 07FEFFFFFH;
	  END;
          RETURN dblwrd.dbl;
      END MaxReal;

      PROCEDURE MinShortReal() : REAL;
      BEGIN
	  dblwrd.lo := 0FF7FFFFFH;
          RETURN FLOAT(dblwrd.flt);
      END MinShortReal;

      PROCEDURE MaxShortReal() : REAL;
      BEGIN
	  dblwrd.lo := 07F7FFFFFH;
          RETURN FLOAT(dblwrd.flt);
      END MaxShortReal;
 * ---------------------------------------- *)

      CONST asciiOffset = 40B;
      TYPE  StdProcSet = SET OF StandardProcs;
      VAR curs : ElemPtr;
          parX : ExprDesc;
          newP : ExprDesc;
          val  : CARDINAL;
          typ  : TypeDesc;
          id   : IdDesc;
          ch   : CHAR;
	  pCls : TyNodeClass;
	  comp : BOOLEAN;
	  eOrd : BOOLEAN;
	  eLit : BOOLEAN;
	  tOrd : BOOLEAN;

    BEGIN
      InitCursor(exp.paramSeq,curs);
      IF Ended(curs) THEN 
        IF sel = timeP THEN exp.exprType := crdTyPtr;
        ELSE Error(248); exp.exprType := NIL;
        END;
        RETURN;
      END;
      GetNext(curs,parX);
      Assert(parX <> NIL);
 
      IF sel IN StdProcSet{minP,maxP,tsizeP,valP,castP} THEN
        CheckTypeId(parX,typ);
      ELSIF sel = sizeP THEN
        CheckTypeOfDesig(parX,typ);
      ELSE 
	TraverseExp(parX);
      END;
      CASE sel OF
      | lengthP :
	  IF parX^.exprType <> NIL THEN
	    IF parX^.exprType^.tyClass IN TyClassSet{S1,SS} THEN
              exp.exprClass := literalNode;
              exp.conValue.fixValue := parX^.conValue.strHigh;
	    ELSIF (parX^.exprType^.tyClass = arrays) AND
		  (WidenedType(parX^.exprType^.targetType) = chTyPtr) THEN
	      IF parX^.exprType^.isDynamic THEN
		CreateExprDesc(newP,desigNode);
		newP^.exprType := crdTyPtr;
	        newP^.name.variable := parX^.name.variable^.nextHigh;
		IF AccessModeOf(parX^.name) >= uplevel THEN
		  ForceAccessMode(newP^.name,uplevel);
		ELSE 
		  ForceAccessMode(newP^.name,highAccess);
		END;
		LinkRight(exp.paramSeq,newP);
	      ELSE
		CreateExprDesc(newP,literalNode);
		newP^.exprType := crdTyPtr;
(*$T-*)		newP^.conValue.fixValue := IndexCardinality(parX^.exprType) - 1;
(*$T=*)		LinkRight(exp.paramSeq,newP);
	      END;
	    ELSIF (parX^.exprType^.tyClass <> stringTs) OR
		  (WidenedType(parX^.exprType^.targetType) <> chTyPtr) THEN
	      Error(214);
	    END;
	  END;
	  exp.exprType := PointerTo(ZZ);
      | absP   :
	  IF parX^.exprType <> NIL THEN
	    WITH exp DO
              (* result type is same, except that subranges go to host *)
              exprType := WidenedType(parX^.exprType);
              pCls := exprType^.tyClass;  (* class of widened type *)
	      IF parX^.exprClass = literalNode THEN
                exp := parX^; (* overwrite the expression descriptor *)
                CASE pCls OF
                | ZZ, UU   : (* hey, alright already! *)
                | II, ints :
                    IF conValue.intValue = MIN(INTEGER) THEN Error(215);
                    ELSE conValue.intValue := ABS(conValue.intValue);
                    END;
                    exprType := PointerTo(ZZ);
                | doubles,floats,RR :
                    conValue.floatValue := ABS(conValue.floatValue);
                    exprType := rrTyPtr;
                ELSE Error(214);
                END;
	      ELSIF NOT (pCls IN numeric) THEN Error(214);
              END;
	    END (* WITH exp *) ;
	  END;
      | floatP,lfloatP,sfloatP :
          IF parX^.exprType <> NIL THEN
	    (*  first set the out type ... *)
	    IF sel = sfloatP THEN
	      exp.exprType := fltTyPtr;
	    ELSE
	      exp.exprType := dblTyPtr;
	    END;
	    (* now check the param class *)
	    pCls := GetTyClass(parX); 		(* kjg 14-Jul-91 *)
            IF NOT (pCls IN numeric) THEN
	      Error(214);
	    ELSE (* check for literals *)
	      IF (parX^.exprClass = literalNode) THEN
                IF (pCls IN
		       TyClassSet{II,ints}) THEN
		  WITH parX^.conValue DO floatValue := FLOAT(intValue) END;
                ELSIF (pCls IN
		       TyClassSet{ZZ,UU,cards}) THEN
		  WITH parX^.conValue DO floatValue := FLOAT(fixValue); END;
		  (* else already a literal double value *)
		END;
		parX^.exprType := rrTyPtr;
		exp := parX^;
	        (* 
	         *  Note that the code generator is responsible for
	         *  the float <--> double conversion of literals. At
	         *  this stage all literals are the (double) RR format.
	         *)
	      END;
	    END;
	  END;
      | truncP :
          IF parX^.exprType <> NIL THEN
	    IF NOT (parX^.exprType^.tyClass IN realSet) 
	    THEN Error(214);
	    ELSE 
	      IF (parX^.exprClass = literalNode) THEN
	        IF ((parX^.conValue.floatValue <= -1.0)  OR
		    (parX^.conValue.floatValue >= FLOAT(MAX(CARDINAL)) + 1.0))
		  THEN Error(215);
	        ELSE
		  WITH parX^.conValue DO fixValue := TRUNC(floatValue); END;
		  exp := parX^;
		END;
	      END;
	    END;
	  END;
	  exp.exprType := crdTyPtr;
      | rotateP, shiftP :
	  IF parX^.exprType <> setTyPtr THEN Error(214) END;
          IF Ended(curs) THEN Error(248); RETURN END;
          GetNext(curs,parX);
          TraverseExp(parX);
	  IF  (sel = rotateP) AND
	      (parX^.exprClass = literalNode) THEN
	    parX^.conValue.fixValue := 
		parX^.conValue.fixValue MOD bitsInWord;
	  END;
	  CheckedAssignCompatible(parX,intTyPtr,comp);
	  IF NOT comp THEN Error(253) END;
	  exp.exprType := setTyPtr;
      | entierP, roundP :
          IF parX^.exprType <> NIL THEN
	    IF NOT (parX^.exprType^.tyClass IN realSet) THEN
	      Error(214);
	    ELSIF (parX^.exprClass = literalNode) THEN
	      IF sel = entierP THEN
	        IF (parX^.conValue.floatValue < FLOAT(MIN(INTEGER)))  OR
		  (parX^.conValue.floatValue >= FLOAT(MAX(INTEGER))+1.0) THEN
		  Error(215);
 		ELSE
 		  WITH parX^.conValue DO intValue := ENTIER(floatValue); END;
 		  exp := parX^;
	        END;
	      ELSE (* roundP *)
	        IF (parX^.conValue.floatValue <= FLOAT(MIN(INTEGER))-0.5)  OR
		  (parX^.conValue.floatValue >= FLOAT(MAX(INTEGER))+0.5) THEN
		  Error(215);
 		ELSE
 		  WITH parX^.conValue DO intValue := ROUND(floatValue); END;
 		  exp := parX^;
	        END;
	      END;
	    END;
	  END;
	  exp.exprType := intTyPtr;
      | hentierP, hroundP, htruncP :
          IF parX^.exprType <> NIL THEN
	    IF NOT (parX^.exprType^.tyClass IN realSet) THEN Error(214) END;
	  END;
	  exp.exprType := hugeTyPtr;
      | timeP  : Error216(curs); (* should have no params *)
      | capP   : (* do literals, leave rest *)
          IF parX^.exprType <> NIL THEN
            IF GetTyClass(parX) IN TyClassSet{chars,S1} THEN
              (* now check, is it a literal? *)
              IF parX^.exprClass = literalNode THEN
                ch := parX^.conValue.charValue;
                IF (ch >= 'a') AND (ch <= 'z') THEN
                  ch := CHR(ORD(ch) - asciiOffset);
                  parX^.conValue.charValue := ch;
                END; (* now get rid of the func call *)
                exp := parX^;
              END;
            ELSE Error(263);
            END;
          END;
          (* set the result type anyway *)
          exp.exprType := chTyPtr;
      | chrP   : (* do literals, leave rest *)
          (* set the result type anyway *)
          exp.exprType := chTyPtr;
          IF IsOrdinalType(parX^.exprType) THEN
            IF parX^.exprClass = literalNode THEN
              WITH parX^ DO
                val := OrdinalValue(exprType,conValue);
		(* this next catches all negatives also ! *)
                IF val <= charMax THEN 
                  conValue.charValue := CHR(val);
		  conValue.stringIx  := 0;	(* jl Oct 95 *)
		  conValue.strHigh   := 1;	(* jl Oct 95 *)
                ELSE Error(215); (* out of range *)
                END;
              END;
              exp := parX^;
              exp.exprType := PointerTo(S1);
	    ELSIF TypesOverlap(chTyPtr,parX^.exprType) THEN
	      EXCL(parX^.testFlags,rangeTests);
            END;
	  ELSIF parX^.exprType = hugeTyPtr THEN
          ELSE Error(206); (* not ordinal *)
          END;
      | highP  :
        (* 
         *  if ok, must replace the proc call by the param. desigNode;
         *)
	  IF  (parX^.exprType <> NIL) AND 
	      (parX^.exprType^.tyClass = stringTs) THEN
	    exp.exprType := intTyPtr;
	  ELSE
            CheckDesignator(parX,id);
            IF id <> NIL THEN
              IF  (id^.idClass = varNode)         AND
                  (id^.varType^.tyClass = arrays) AND
                   id^.varType^.isDynamic         THEN
	        GetHighDescriptor(parX^.name,id);
	        IF id = NIL THEN Error(262) END;
                IF  AccessModeOf(parX^.name) >= uplevel THEN
	  	  InitDesignator(parX^.name);
                  ForceAccessMode(parX^.name,uplevel);
                ELSE 
	  	  InitDesignator(parX^.name);
		  ForceAccessMode(parX^.name,highAccess);
                END;
                parX^.name.variable := id;
                parX^.exprType := crdTyPtr;
                exp := parX^;
              ELSE Error(262);
              END;               
            END;               
          END;
      | minP, maxP :
          WITH exp DO
	    IF typ <> NIL THEN
	      IF typ^.tyClass = hInts THEN
	        exprType := PointerTo(hInts);
	      ELSIF typ^.tyClass = floats THEN
                exprClass := literalNode;
	        exprType  := PointerTo(RR);
                IF sel = minP THEN
                  conValue.floatValue := MIN(SHORTREAL); (* MinShortReal(); *)
                ELSE
	          conValue.floatValue := MAX(SHORTREAL); (* MaxShortReal(); *)
                END;
	      ELSIF typ^.tyClass = doubles THEN
                exprClass := literalNode;
	        exprType  := PointerTo(RR);
                IF sel = minP THEN
                  conValue.floatValue := MIN(REAL); (* MinReal(); *)
                ELSE
	          conValue.floatValue := MAX(REAL); (* MaxReal(); *)
                END;
	      ELSE		(* Min/MaxOfOrdType flags non-ord types *)
                exprClass := literalNode;
                IF IsOrdinalType(typ) THEN exprType := typ ELSE exprType := NIL
		END;
                IF sel = minP THEN
                  conValue.fixValue := MinOfOrdType(typ);
                ELSE
	          conValue.fixValue := MaxOfOrdType(typ);
                END;
                (*
                 * now fix up chars & subranges thereof (kjg, jan, aug 89)
                *)
	        FixTypeAndValue(conValue,exprType);
	      END;
            ELSE exprType := NIL;	(* inhibit later error messages *)
            END;
          END;
      | oddP   :
          IF IsOrdinalType(parX^.exprType) THEN
	    (* ! what about chars here, can you take ODD('a') ??? *)
            IF parX^.exprClass = literalNode THEN
              parX^.conValue.fixValue :=
                ORD(ODD(parX^.conValue.fixValue));
              exp := parX^;
            END;
          ELSE Error(206); (* not ordinal *)
          END;
          (* set the result type anyway *)
          exp.exprType := boolTyPtr;
      | ordP   :
          IF IsOrdinalType(parX^.exprType) THEN
            IF parX^.exprClass = literalNode THEN
              WITH parX^ DO
                conValue.fixValue := OrdinalValue(exprType,conValue);
	        IF IsSignedType(exprType) AND
		   (conValue.fixValue > MAX(INTEGER)) THEN Error(215) END;
              END;
              exp := parX^;
            END;
          ELSE Error(206);
          END;
          exp.exprType := crdTyPtr;
      | intP   :
	  IF IsOrdinalType(parX^.exprType) THEN
            IF parX^.exprClass = literalNode THEN
              WITH parX^ DO
                conValue.fixValue := OrdinalValue(exprType,conValue);
	        IF NOT IsSignedType(exprType) AND
		   (conValue.fixValue > MAX(INTEGER)) THEN Error(215) END;
              END;
              exp := parX^;
	    END;
	  ELSIF parX^.exprType^.tyClass IN realSet THEN
	    IF parX^.exprClass = literalNode THEN
	      WITH parX^ DO
	        IF ((conValue.floatValue <= FLOAT(MIN(INTEGER))-1.0)  OR
		    (conValue.floatValue >= FLOAT(MAX(INTEGER))+1.0)) THEN 
 		  Error(215);
		ELSE
		  conValue.intValue := INT(conValue.floatValue);
		END;
	      END;
	      exp := parX^;
	    END;
          ELSIF parX^.exprType <> hugeTyPtr THEN Error(214); 
	  END;
          exp.exprType := intTyPtr;
      | hugeP   :
	  IF NOT((parX^.exprType^.tyClass IN numeric) OR
			IsOrdinalType(parX^.exprType)) THEN Error(214) END;
          exp.exprType := hugeTyPtr;
      | sizeP, tsizeP :
	  WITH exp DO
	    exprClass := literalNode;
	    exprType  := PointerTo(ZZ); (* ISO, Linz, D92 *)
	    IF typ <> NIL THEN 
	      conValue.fixValue := typ^.size;
(*	      IF conValue.fixValue = 0 THEN Error(497) END; *)
	    END;
	  END;
	  IF (sel = tsizeP) AND NOT Ended(curs) THEN
	    GetNext(curs,parX);
	    lastPos := parX^.sourceLoc;
	    Error(499); (* tags are ignored *)
	    WHILE NOT Ended(curs) DO GetNext(curs,parX) END;
	  END;
      | valP   :
          IF Ended(curs) THEN Error(248);
          ELSE
	    IF typ = NIL THEN RETURN END; (* Error(204) *)
            IF NOT (typ^.tyClass IN numeric) AND
               NOT IsOrdinalType(typ) THEN
	      Error(218); exp.exprType := NIL; RETURN;
	    END;
            exp.exprType := typ;
            GetNext(curs,parX);
            TraverseExp(parX);
	    IF parX^.exprType = NIL THEN RETURN END;
            IF NOT (parX^.exprType^.tyClass IN numeric) AND
               NOT IsOrdinalType(parX^.exprType) THEN
	      Error(218); exp.exprType := NIL; RETURN;
	    END;
	   (*
	    *  set some flags for later
	    *)
	    tOrd := IsOrdinalType(typ);
	    eOrd := IsOrdinalType(parX^.exprType);
	    eLit := parX^.exprClass = literalNode;
            IF eOrd THEN
	      IF eLit THEN
	        WITH parX^ DO
		(*
		 *  parX might not be assign compat with typ,
		 *  so we must do some tricky stuff here
		 *)
		  val := OrdinalValue(exprType,conValue);
		  (* overwrite expr descriptor *)
		  exp.exprClass := literalNode;
		  exp.exprType  := WidenedType(typ);
		  IF exp.exprType = chTyPtr THEN
		    IF val > charMax THEN (* give error, stop test *)
		      Error(215); exp.exprType := typ;
		    ELSE 
		      exp.conValue.charValue := CHR(val);
		      RangeCheckC(exp,typ);
		    END;
		  ELSIF tOrd THEN
		    exp.conValue.fixValue := val;
		    RangeCheckC(exp,typ);
		  ELSIF exp.exprType = hugeTyPtr THEN (* ord --> huge *)
		    exp.conValue.fixValue := val;
		   (* no fold here yet *)
		  ELSE 
                    IF (exprType <> NIL) AND (exprType^.tyClass = II) THEN
                      exp.conValue.floatValue := FLOAT(conValue.intValue);
                    ELSE
                      exp.conValue.floatValue := FLOAT(conValue.fixValue);
                    END;
		    exp.exprType := rrTyPtr;
		  END;
	        END; (* with *)
	      ELSIF tOrd AND TypesOverlap(typ,parX^.exprType) THEN
	       (*
		*  the ordinal to ordinal case...
		*)
	        EXCL(parX^.testFlags,rangeTests);
	      END; (* else nothing *)
	    ELSIF parX^.exprType = hugeTyPtr THEN 
(* do the literal folds later *)
	    ELSE (* exp is a floating point value *)
	      IF eLit THEN
		exp.exprType := WidenedType(typ);
		exp.exprClass := literalNode;
	        WITH parX^ DO
		  IF exp.exprType = intTyPtr THEN
		    IF (conValue.floatValue <= FLOAT(MIN(INTEGER))-1.0) OR
		       (conValue.floatValue >= FLOAT(MAX(INTEGER))+1.0) THEN 
		      Error(215);
		    ELSE
		      exp.conValue.intValue := INT(conValue.floatValue);
		      RangeCheckC(exp,typ);
		    END;
		  ELSIF tOrd THEN (* unsigned ordtypes *)
		    IF (conValue.floatValue <= -1.0 )  OR
		       (conValue.floatValue >= FLOAT(MAX(CARDINAL))+1.0) THEN 
		      Error(215);
		    ELSIF exp.exprType = chTyPtr THEN
		      val := TRUNC(conValue.floatValue);
		      IF val > charMax THEN (* give error, stop test *)
			Error(215);
		      ELSE exp.conValue.charValue := CHR(val);
		      END;
		    ELSE
		      exp.conValue.fixValue := TRUNC(conValue.floatValue);
		    END;
		    RangeCheckC(exp,typ);
		  ELSE
		    exp.exprType := rrTyPtr;
		    exp.conValue.floatValue := conValue.floatValue;
		  END;
		END;
	      END;
	      IF tOrd THEN
	       (*
		*  the floating to ordinal case...
		*  Don't do a range check if the 
		*  conversion check does it all.
		*)
		IF (typ = intTyPtr) OR 
		   (typ = crdTyPtr) THEN
	          EXCL(parX^.testFlags,rangeTests);
		END;
	      END;
	    END;
          END;
	  IF NOT Wg13ValRules(typ,parX^.exprType) THEN Error(510) END;
      | adrP   :
          CheckDesignator(parX,id);
          IF (id <> NIL) AND (id^.idClass = varNode) THEN
            exp.exprClass := adrDesigNode; (* signals ADR() *)
            exp.name      := parX^.name;   (* = first param *)
(* 
 *  Here the argument is that the taking of the address
 *  threatens the variable, even if the statement is not
 *  in within the span of control of the for loop variable
 *  Fixed on 2-Nov-90 to unconditionally set uplevelThreat (kjg)
 *)
	    INCL(exp.name.variable^.varUseSet,varParThr);
	    INCL(exp.name.variable^.varUseSet,uplevThr);
	    IF IsFORThreat(exp.name.variable) THEN Error(297) END;
	  ELSE Error(255); (* must be variable *)
          END;
          exp.exprType := adrTyPtr;
      | addAdrP, subAdrP, difAdrP :
	  IF NOT Compatible(parX^.exprType,adrTyPtr) THEN Error(294) END;
	  IF Ended(curs) THEN Error(248);
	  ELSE
	    GetNext(curs,parX); TraverseExp(parX);
	    IF sel = difAdrP THEN
	      IF NOT Compatible(parX^.exprType,adrTyPtr) THEN Error(294);
	      ELSE exp.exprType := intTyPtr;
	      END;
	    ELSIF Compatible(parX^.exprType,crdTyPtr) THEN 
	      exp.exprType := adrTyPtr;
	    ELSE Error(214);
	    END;
	  END;
      | castP  :
          IF Ended(curs) THEN Error(248);
          ELSE
            GetNext(curs,parX);
            MakeCast(exp,typ,parX);
          END;
      END;
      IF NOT Ended(curs) THEN Error216(curs) END;
    END StFuncCheck;

    PROCEDURE RecordRangeSeq(VAR recExpr : ExprDesc);
      VAR field : IdDesc;
	  elem  : RangeDesc;
	  conPtr : ConBlock;
	  elemCurs, fieldCurs : ElemPtr;
	  nonLitSeq : Sequence; 		(* of RangeDesc *)
	  ended, errors, compat : BOOLEAN;	(* Oct 92	*)
	  ix : CARDINAL;
    BEGIN 
      (* Assert: recExpr^.exprType^.tyClass = records
       *
       *   Initialize traversals and flags
       *)
      InitCursor(recExpr^.exprType^.fieldSeq,fieldCurs);
      InitCursor(recExpr^.rangeSeq,elemCurs);
      ended := Ended(fieldCurs) OR Ended(elemCurs);
       (*
	*   Do traversals
	*)
      WHILE NOT ended DO
	GetNext(fieldCurs,field);
	GetNext(elemCurs,elem);
	(*
	 *  must test if this is a nested constructor of
	 *  anonymous type, if so send presumed type
	 *)
	IF  (elem^.lower^.exprClass = constructorNode) AND
	    EmptySelList(elem^.lower^.name) THEN
	  elem^.lower^.exprType := field^.fieldType;
	END;
        TraverseExp(elem^.lower); 
        IF elem^.upper <> NIL THEN
	  IF elem^.upper^.exprClass = repCountNode THEN 
	    Error(316);
	  ELSE Error(315);
	  END;
	  errors := TRUE;
	END;
	CheckedAssignCompatible(elem^.lower,field^.fieldType,compat);
	IF NOT compat THEN Error(258); errors := TRUE END;
        ended := Ended(fieldCurs) OR Ended(elemCurs);
      END;
      (*
       *   Check for normal termination
       *)
      IF NOT Ended(elemCurs) THEN Error(314);
      ELSIF NOT Ended(fieldCurs) THEN Error(313);
      ELSE
	(* 
	 *   Construct constructor 
	 *)
	conPtr := NIL;
	InitSequence(nonLitSeq);
	InitCursor(recExpr^.exprType^.fieldSeq,fieldCurs);
	InitCursor(recExpr^.rangeSeq,elemCurs);
	WHILE NOT Ended(elemCurs) DO
	  GetNext(elemCurs,elem);
	  GetNext(fieldCurs,field);
	  IF elem^.lower^.exprClass = literalNode THEN
	    IF conPtr = NIL THEN (* for constant part *)
	      ALLOCATE(conPtr,recExpr^.exprType^.size);
	      FOR ix := 0 TO recExpr^.exprType^.size - 1 DO  (* jl Jun 94 *)
		conPtr^[ix] := 0C;
	      END;
	    END;
	    CopyConstant(elem^.lower^.conValue,
			 elem^.lower^.exprType,
	  		 field^.fieldType,
			 ADR(conPtr^[field^.fieldOffset]));
	  ELSE (* non literal expression *)
	    elem^.elemOffset := field^.fieldOffset;
	    elem^.desigType  := field^.fieldType;
	    LinkRight(nonLitSeq,elem);
	  END;
	END; (* while *)
	IF IsEmpty(nonLitSeq) THEN (* previously the only case !! *)
	  recExpr^.exprClass := literalNode;
	  recExpr^.conValue.adrsValue := conPtr;
	ELSE (* the mixed case *)
	  IF conPtr <> NIL THEN (* not ALL non-literal *)
	    elem := MakeRangeDesc(NIL,NIL);
	    elem^.elemOffset := 0;
            elem^.desigType  := recExpr^.exprType;
            CreateExprDesc (elem^.lower,literalNode);
            elem^.lower^.exprType := recExpr^.exprType;
            elem^.lower^.conValue.adrsValue := conPtr;
	    LinkLeft(nonLitSeq,elem);
	  END;
	  DisposeList(recExpr^.rangeSeq);
	  recExpr^.rangeSeq := nonLitSeq;
	END;
      END;  (* outer if *)
    END RecordRangeSeq;

    PROCEDURE ArrayRangeSeq(VAR arrExpr : ExprDesc);
      VAR eCount     : CARDINAL;
	  elem       : RangeDesc;
	  currOffset : CARDINAL;
	  elemType   : TypeDesc;
	  elemCurs   : ElemPtr;
	  compat     : BOOLEAN;
	  errors     : BOOLEAN;
	  conPtr     : ConBlock;
(* and the following new stuff Oct 92 *)
	  nonLitSeq  : Sequence; (* of RangeDesc *)
    BEGIN
      Assert(arrExpr^.exprType^.tyClass = arrays);
      (*
       *   Initialize traversals and flags
       *)
      elemType := arrExpr^.exprType^.elementType;
      InitCursor(arrExpr^.rangeSeq,elemCurs);
      errors := FALSE; eCount := 0;
       (*
	*   Do traversal
	*)
      WHILE NOT Ended(elemCurs) DO
	GetNext(elemCurs,elem);
	(*
	 *  must test if element is a nested constructor of
	 *  anonymous type, if so send presumed type
	 *)
	IF  (elem^.lower^.exprClass = constructorNode) AND
	    EmptySelList(elem^.lower^.name) THEN
	  elem^.lower^.exprType := elemType;
	END;
        TraverseExp(elem^.lower); 
        IF elem^.upper = NIL THEN
	  INC(eCount);
	ELSIF elem^.upper^.exprClass = repCountNode THEN 
	  INC(eCount,elem^.upper^.count);
	ELSE Error(315); (* ranges only allowed for sets *)
	END;
	CheckedAssignCompatible(elem^.lower,elemType,compat);
	IF NOT compat THEN Error(258); errors := TRUE END;
      END; (* end while *)
       (*
	*  Check for normal termination
	*)
      IF eCount = IndexCardinality(arrExpr^.exprType) THEN
        IF NOT errors THEN 
	  (* 
	   *   Construct constant 
	   *)
	  conPtr := NIL;
	  InitSequence(nonLitSeq);
	  currOffset := 0;
	  InitCursor(arrExpr^.rangeSeq,elemCurs);
	  WHILE NOT Ended(elemCurs) DO
	    GetNext(elemCurs,elem);
	    IF (conPtr = NIL) AND
	       (elem^.lower^.exprClass = literalNode) THEN
	      ALLOCATE(conPtr,arrExpr^.exprType^.size);
	    END;
	    IF elem^.upper <> NIL THEN  (* multiple assigns ... *)
	      IF elem^.lower^.exprClass <> literalNode THEN
		elem^.elemOffset := currOffset;
		elem^.desigType  := elemType;
		LinkRight(nonLitSeq,elem);
	        INC(currOffset,elemType^.size * elem^.upper^.count);
	      ELSE
	        FOR eCount := 1 TO elem^.upper^.count DO
	         (*
	          *   replicate constant elem^.upper^.count times
	          *)
		  CopyConstant(elem^.lower^.conValue,
			       elem^.lower^.exprType,
	                       elemType,
		               ADR(conPtr^[currOffset]));
	          INC(currOffset,elemType^.size);
		END;
	      END; (* if literal *)
	    ELSE (* single element only ... *)
	      IF elem^.lower^.exprClass = literalNode THEN
	        CopyConstant(elem^.lower^.conValue,
			     elem^.lower^.exprType,
			     elemType,
		             ADR(conPtr^[currOffset]));
	      ELSE
	        elem^.desigType  := elemType;
	        elem^.elemOffset := currOffset;
	        LinkRight(nonLitSeq,elem);
	      END;
	      INC(currOffset,elemType^.size);
	    END; (* end if upper = NIL *)
	  END; (* while *)
	  Assert(currOffset = arrExpr^.exprType^.size);
	  IF IsEmpty(nonLitSeq) THEN (* previously the only case !! *)
	    arrExpr^.exprClass := literalNode;
	    arrExpr^.conValue.adrsValue := conPtr;
	  ELSE (* the mixed case *)
	    IF conPtr <> NIL THEN (* not ALL non-literal *)
	      elem := MakeRangeDesc(NIL,NIL);
              elem^.elemOffset := 0;
	      elem^.desigType  := arrExpr^.exprType;
              CreateExprDesc (elem^.lower, literalNode);
              elem^.lower^.exprType := arrExpr^.exprType;
              elem^.lower^.conValue.adrsValue := conPtr;
	      LinkLeft(nonLitSeq,elem);
	    END;
	    DisposeList(arrExpr^.rangeSeq);
	    arrExpr^.rangeSeq := nonLitSeq;
	  END;
	END (* if not errors *)
      ELSIF eCount < IndexCardinality(arrExpr^.exprType) THEN 
	Error(313);
      ELSE Error(314);
      END;
    END ArrayRangeSeq;

    PROCEDURE SetRangeSeq (VAR setExpr : ExprDesc);
    (*
     *  Process the sequence of ranges which construct a set designator.
     *  Check compatibility with base type, and construct a constant if 
     *  possible; constant code follows that in M2ExpParser.SetConstrC.
     *)
    VAR
	rngCurs  : ElemPtr;
        baseType : TypeDesc;
        literals, errors : BOOLEAN;
        range : RangeDesc;
        lo, hi, min, max : CARDINAL;
        constValue : LexAttType;
        newRangeSeq : Sequence;
        unionExpr : ExprDesc;
	exclLoTst : BOOLEAN;

    BEGIN
      setExpr^.exprClass := setDesigNode; (* now we KNOW it is a set *)
      baseType := setExpr^.exprType^.baseType;
      IF baseType <> NIL THEN 
        WITH baseType^ DO
          CASE tyClass OF (* always unsigned! *)
          | subranges : min := minRange; max := maxRange;
          | enums     : min := 0; max := cardinality - 1;
          | chars     : min := 0; max := charMax;
          | bools     : min := 0; max := 1;
          END;
        END;
        errors := FALSE;
      ELSE min := 0; max := cardMax; errors := TRUE;
      END; (* if baseType <> NIL *)

      (* Process the sequence of members or member ranges *)
      WITH setExpr^ DO
        InitCursor  (rangeSeq, rngCurs);
        (*
         *  there is a special case here: if this is the empty
         *  set then the sequence is empty. In this case the
         *  constructorNode is replaced by a literal even though
         *  no constant range selector elements are found
         *)
        literals := Ended(rngCurs);
        WHILE NOT Ended(rngCurs) DO
          GetNext (rngCurs, range);
	  exclLoTst := FALSE;
          WITH range^ DO
            TraverseExp (lower);
            IF NOT Compatible(baseType, lower^.exprType) THEN
              Error (207); errors := TRUE;
            ELSE
              (* If a literal, check for later constant folding *)
              IF (lower^.exprClass = literalNode) THEN
	        exclLoTst := TRUE;
                lo := OrdinalValue(lower^.exprType, lower^.conValue);
                IF (lo < min) OR (lo > max) THEN
                  Error (215); errors := TRUE;
                END;
	      ELSIF TypesOverlap(baseType,lower^.exprType) THEN
	        exclLoTst := TRUE;
              END;
            END;
            IF upper <> NIL THEN
              TraverseExp (upper);
              IF NOT Compatible(baseType, upper^.exprType) THEN
                Error (207); errors := TRUE;
              ELSE
		(*
		 *  it is possible that the lower expression
		 *  is always in range but still requires 
		 *  range testing against the upper limit
		 *)
                IF (upper^.exprClass = literalNode) THEN
		  EXCL(upper^.testFlags,rangeTests);
                  hi := OrdinalValue(upper^.exprType, upper^.conValue);
                  IF (hi < min) OR (hi > max)
                    THEN Error (215); errors := TRUE;
                  END;
                  IF lower^.exprClass = literalNode THEN (* lo is set *)
                    IF lo > hi THEN Error (209); errors := TRUE; END;
                    literals := TRUE;
		    EXCL(lower^.testFlags,rangeTests);
                  END;
		ELSIF TypesOverlap(baseType,upper^.exprType) THEN
		  EXCL(upper^.testFlags,rangeTests);
                END;
              END;
            ELSE (* range^.upper = NIL ==> single value *)
              literals := literals OR (lower^.exprClass = literalNode);
	      IF exclLoTst THEN
		EXCL(lower^.testFlags,rangeTests);
	      END;
            END;
          END (* WITH range^ *) ;
        END (* WHILE NOT Ended *) ;

        (* If some constant elements and no errors, construct a constant *)
        IF literals AND (NOT errors) THEN
          MakeEmptySet(setExpr^.exprType^.size, constValue.patternIx); 
	  Commit ();
          InitSequence (newRangeSeq);
          InitCursor (rangeSeq, rngCurs);
          WHILE NOT Ended(rngCurs) DO
            GetNext (rngCurs, range);
            WITH range^ DO
              (* If a literal, fold it into single literal *)
              IF (lower^.exprClass = literalNode) AND
                 ((upper = NIL) OR (upper^.exprClass = literalNode)) THEN
                lo := OrdinalValue(lower^.exprType, lower^.conValue);
                IF upper <> NIL THEN
                  hi := OrdinalValue(upper^.exprType, upper^.conValue);
                  SetRngIncl (constValue.patternIx, lo, hi);
                  DEALLOCATE (upper, TSIZE(ExprRec));
                ELSE (* range^.upper = NIL - single value *)
                  SetInclude (constValue.patternIx, lo);
                  DEALLOCATE (lower, TSIZE(ExprRec));
                END;
                DEALLOCATE (range, TSIZE(RangeRec));
                (* ! is this safe - GenSeqSupp? *)
              ELSE (* not entirely literal *)
                LinkRight (newRangeSeq, range);
              END;
            END (* WITH range^ *) ;
          END (* WHILE NOT Ended *) ;
          DisposeList (rangeSeq);

          IF IsEmpty(newRangeSeq) THEN
            (* All literal - replace constructorNode with literalNode *)
            (* ! size safe? *)
            exprClass := literalNode;
            conValue := constValue;
          ELSE
            (* Mixed literal and variable - construct set union node with 
               literal as left operand and set designator with new range
               sequence as right operand, rightOp gets old testFlags     *)
            CreateExprDesc (unionExpr, plusNode);
            WITH unionExpr^ DO
	      exprType := setExpr^.exprType;
              CreateExprDesc (leftOp, literalNode);
              leftOp^.exprType := exprType;
              leftOp^.conValue := constValue;
              rightOp := setExpr;
              rightOp^.rangeSeq := newRangeSeq;
            END;
            setExpr := unionExpr;
          END;
        END (* of IF constants and (NOT errors) *) ;
      END (* of WITH setExpr^ *) ;
    END SetRangeSeq;

  BEGIN (* TraverseExp *)
    (* Note: CreateExprDesc has set exprType to bools (for Boolean and 
     * relational operators) or NIL; in error situations, these defaults are 
     * intended to allow further checking of apparently Boolean results, and 
     * to avoid parasitic error generation otherwise. *) 
  origExp := exp;
  WITH origExp^ DO
    lastPos := sourceLoc;
    CASE exprClass OF
    | negateNode :
        TraverseExp(notOp);
        IF notOp^.exprType <> NIL THEN
         (* check for signed type *)
          class := GetTyClass(notOp);
          IF class IN (numeric - TyClassSet{cards}) THEN
            IF notOp^.exprClass = literalNode THEN
              Negate(notOp^.exprType, notOp^.conValue);
              exp^ := notOp^;
            ELSE exprType := WidenedType(notOp^.exprType);
            END;
          ELSE Error (268);
          END;
        END;
    | notNode :
        TraverseExp(notOp);
        IF notOp^.exprType <> NIL THEN
          (* Allow for subrange of Boolean, even though it is pretty 
             pointless, and don't check for illegal NOT of proper subrange *)
          IF GetTyClass(notOp) = bools THEN
            IF notOp^.exprClass = literalNode THEN
              WITH notOp^.conValue DO
                fixValue := (fixValue + 1) MOD 2;
              END;
              exp^ := notOp^;
            (* ELSE exprType = bools by default *)
            END;
          ELSE Error (269);
          END;
        END;
    | andNode, orNode :
        TraverseExp(leftOp);
        TraverseExp(rightOp);
        IF (leftOp^.exprType <> NIL) AND (rightOp^.exprType <> NIL) THEN
          IF (GetTyClass(leftOp) = bools) AND 
	     (GetTyClass(rightOp) = bools) THEN
            IF (leftOp^.exprClass = literalNode) AND
               (rightOp^.exprClass = literalNode) THEN
(* !          BoolOps (VAL(TerminalSymbols,exprClass), 
 *                     leftOp^.conValue.fixValue, rightOp^.conValue.fixValue); 
 *)
              Operation (VAL(TerminalSymbols,ORD(exprClass)),
                         leftOp^.exprType, rightOp^.exprType, 
                         leftOp^.conValue, rightOp^.conValue);
              (* assert: no Commit necessary for bools *)
              DEALLOCATE (rightOp, TSIZE(ExprRec));
              exp^ := leftOp^;
            (* ELSE exprType = bools by default *)
            END;
          ELSE ExpErr (exp,269);
          END;
        END;
    | divNode .. minusNode :
        TraverseExp(leftOp);
        TraverseExp(rightOp);
        IF (leftOp^.exprType <> NIL) AND (rightOp^.exprType <> NIL) THEN
          IF NOT Compatible(leftOp^.exprType, rightOp^.exprType) THEN
            ExpErr (exp,220);
          ELSE
            leftClass := GetTyClass(leftOp);
            IF NOT (leftClass IN (numeric + TyClassSet{S1,SS,sets})) THEN
              ExpErr (leftOp,270);
            ELSE
              (* If both literals, check compatibility with operator
	       * and fold using M2CompOperations.Operation *)
              IF (leftOp^.exprClass = literalNode) AND
                 (rightOp^.exprClass = literalNode) THEN
                Operation (VAL(TerminalSymbols,ORD(exprClass)), 
                           leftOp^.exprType, rightOp^.exprType,
                           leftOp^.conValue, rightOp^.conValue);
                (*
                 * could be a new set has been constructed, so...
                *)
                Commit; (* make result permanent *)
                DEALLOCATE (rightOp, TSIZE(ExprRec));
                exp^ := leftOp^;
              ELSE (* not both literals - check valid operator *)
                IF (leftClass IN TyClassSet{RR,sets,floats,doubles}) AND
                   (exprClass IN ExClassSet{divNode,modulusNode,remNode}) THEN
                  ExpErr (leftOp,271);
                ELSE (* valid operator - generate result type *)
                  IF leftClass IN 
			TyClassSet{sets,ints,cards,hInts,floats,doubles} THEN
                    exprType := WidenedType(leftOp^.exprType);
                  ELSE
		    exprType := WidenedType(rightOp^.exprType);
                  END;
		  (* now checks for division operators *)
		  IF exprClass IN
		     ExClassSet{slashNode,remNode,divNode,modulusNode} THEN
		    (* divide by literal zero? *)
		    IF (rightOp^.exprType^.tyClass = ZZ) AND 
		       (rightOp^.conValue.fixValue = 0) THEN
		      ExpErr(leftOp,490);		(* jl Oct 95 *)
		    ELSIF (rightOp^.exprType^.tyClass = RR) AND
			  (rightOp^.conValue.floatValue = 0.0) THEN
		      ExpErr(leftOp,490);		(* jl Oct 95 *)
		    END;
		    (* modulo divide by negative literal? *)
		    IF ((exprClass = modulusNode) OR
			(exprClass = divNode)) AND
		       (rightOp^.exprType^.tyClass = II) THEN
		      ExpErr(leftOp,489);
		    END;
		  END;
                END;
              END;
            END;
          END;
        END;
    | equalsNode .. lessEqNode :
        TraverseExp(leftOp);
        TraverseExp(rightOp);
        IF (leftOp^.exprType <> NIL) AND (rightOp^.exprType <> NIL) THEN
          IF NOT Compatible(leftOp^.exprType, rightOp^.exprType) THEN
            ExpErr (exp,220);
          ELSE
            leftClass := GetTyClass(leftOp);
            IF leftClass IN TyClassSet{arrays,records,unions,SS}
              THEN ExpErr (leftOp,272);
            ELSE
              (* If both literals, check compatibility with operator and fold
                 using M2CompOperations.Operation *)
              IF (leftOp^.exprClass = literalNode) AND
                 (rightOp^.exprClass = literalNode) THEN
                Operation (VAL(TerminalSymbols,ORD(exprClass)), 
                           leftOp^.exprType, rightOp^.exprType,
                           leftOp^.conValue, rightOp^.conValue);
                (* assert: no need to Commit here *)
                DEALLOCATE (rightOp, TSIZE(ExprRec));
                exp^ := leftOp^;
              ELSE (* not both literals - check valid operator *)
                IF (leftClass = sets) AND
                   (exprClass IN ExClassSet{greaterNode,lessNode}) THEN
                  ExpErr (exp,273);
                ELSIF (leftClass IN TyClassSet{adrs,words,bytes,hiddens,
                                opaqueTemp,pointers,procTypes,funcTypes}) AND
                      (exprClass IN ExClassSet{greaterNode..lessEqNode}) THEN
                  ExpErr (exp,274);
             (* ELSE exprType = bools by default *)
                END;
              END;
            END;
          END;
        END;
    | inNode :
        TraverseExp(leftOp);
        TraverseExp(rightOp);
        IF rightOp^.exprType <> NIL THEN
          IF rightOp^.exprType^.tyClass <> sets THEN
            ExpErr (rightOp,275);
          ELSE
            IF leftOp^.exprType <> NIL THEN
              (* If both literals, check compatibility with operator and fold
                 using M2CompOperations.Operation *)
              IF (leftOp^.exprClass = literalNode) AND
                 (rightOp^.exprClass = literalNode) THEN
                Operation (VAL(TerminalSymbols,ORD(exprClass)), 
                           leftOp^.exprType, rightOp^.exprType,
                           leftOp^.conValue, rightOp^.conValue);
                DEALLOCATE (rightOp, TSIZE(ExprRec));
                exp^ := leftOp^;
              ELSE (* not both literals - check compatibility *)
                IF NOT Compatible(leftOp^.exprType,
				rightOp^.exprType^.baseType) THEN 
		  ExpErr (exp,220);
		ELSE
		 (*
		  *  must always do the next, to set rangeTest flag
		  *)
                  CheckedAssignCompatible(leftOp,
				rightOp^.exprType^.baseType,dummy);
                END;
              END;
            END;
          END;
        END;
    | desigNode : (* sometime changes consts to literals ! *)
        BindDesignator(name);
        IF name.variable <> NIL THEN
          id := name.variable;
          CASE id^.idClass OF
          | varNode :
              GetDesigType(name,exprType);
          | constNode :
	      (* Here, it used to be that selector-list was empty *)
              (* this changed because selection allowed on consts *)
	      IF EmptySelList(name) THEN
                exprType  := id^.conType;
                exprClass := literalNode;
                conValue  := id^.conValue;
	      ELSE GetTypeAndValue(exp^);
	      END;
          | procNode, procHeader : (* procedure variable being assigned *)
	      (* Remove bad fix:
	      IF id^.body <> NIL THEN
                INC(id^.body^.refCount);
                INCL(id^.body^.callAttrib,assigned);
              END;
	      *)
              IF NOT EmptySelList(name) THEN Error(243) END;
              exprType := id^.procType;
	      (* Protect this code instead: *)
	      IF NOT (defMod IN modState) THEN
	        IF id^.uphill^.frame <> thisCompileUnit THEN Error(287) END;
	      END;
          | externProc : (* procedure variable being assigned *)
              IF NOT EmptySelList(name) THEN Error(243) END;
              exprType := id^.procType;
          | stFunc, stProc : Error(244);
          ELSE Error(235); exprType := NIL;
          END; (* case *)
        ELSE Error(204);
        END; (* if *)
    | funcDesigNode : (* a function call *)
        BindDesignator(name);
        IF name.variable <> NIL THEN
          id := name.variable;
	  CASE id^.idClass OF
          | varNode, constNode : (* call of function variable ( kjg Nov 92 )*)
	      wrap := FALSE;
              GetDesigType(name,exprType);
              IF  exprType <> NIL THEN
                (* is it a function procedure? *)
                IF exprType^.tyClass = funcTypes THEN
		  IF exprType^.parSiz = infinity THEN
		    exprType^.parSiz := FormalSize(exprType);
		  END;
						 (* fixed kjg 23-Mar-93 *)
		  IF exprType^.parSiz > current^.body^.maxParSize THEN
	            current^.body^.maxParSize := exprType^.parSiz;
		  END;
                  (* check params against formals *)
		  IF (exprType^.parentMod^.idClass = exportNode) AND
		      exprType^.parentMod^.direct THEN
		    CheckDirectParamList(paramSeq, exprType^.params);
		  ELSE
                    CheckActualParamList(wrap, paramSeq, exprType^.params);
		    IF wrap THEN 
                      IF emitCil IN modState THEN
		        M2CilWrappers.MkWrap(name,paramSeq,exprType,current);
                      ELSE
		        M2DcfWrappers.MkWrap(name,paramSeq,exprType,current);
                      END;
		    END;
		  END;
		  IF exprType^.preCon <> NIL THEN 
		   (*
		    *   We pass in the actual parameter sequence, and
		    *   the precondition expression from the TypeDesc.
		    *   We get back the initialisation statement seq,
		    *   and the (possibly modified) actual parameters.
		    *)
		    CreateExprDesc(exp,preconNode);
		    exp^.theCall := origExp;
		    exp^.exprType := exprType^.result;
		    callPos := sourceLoc;
		    CheckPrecon(paramSeq,exprType^.preCon,exp^.evalLst);
		  END;
                  (* expression type is now function result type *)
                  exprType := exprType^.result;
                ELSE Error(260);
                END;
              (* else error already notified by GetDesigType *)
              END;
          | procNode, procHeader, externProc : (* call of function *)
	      RecordCallOf(id);
              IF NOT EmptySelList(name) THEN Error(243);
              ELSE
	        wrap := FALSE;
                IF id^.procType^.tyClass = funcTypes THEN
		  IF (id^.procType^.parentMod^.idClass = exportNode) AND
		      id^.procType^.parentMod^.direct THEN
		    CheckDirectParamList (paramSeq, id^.procType^.params);
		  ELSE
                    CheckActualParamList(wrap, paramSeq, id^.procType^.params);
		    IF wrap THEN 
                      IF emitCil IN modState THEN
		        M2CilWrappers.MkWrap
                                         (name,paramSeq,id^.procType,current);
                      ELSE
		        M2DcfWrappers.MkWrap
                                         (name,paramSeq,id^.procType,current);
                      END;
                    END;
		  END;
		  IF id^.procType^.preCon <> NIL THEN 
		   (*
		    *   We pass in the actual parameter sequence, and
		    *   the precondition expression from the TypeDesc.
		    *   We get back the initialisation statement seq,
		    *   and the (possibly modified) actual parameters.
		    *)
		    CreateExprDesc(exp,preconNode);
		    exp^.theCall := origExp;
		    exp^.exprType := id^.procType^.result;
		    callPos := sourceLoc;
		    CheckPrecon(paramSeq,id^.procType^.preCon,exp^.evalLst);
		  END;
                  exprType := id^.procType^.result;
                ELSE Error(246);
                END
              END;
          | stFunc :
              IF NOT EmptySelList(name) THEN Error(243) END;
              StFuncCheck(id^.procVal,exp^);
          | typeNode : (* obsolete: "type transfer function" *)
              Error(506); (* warning only *)
              IF NOT EmptySelList(name) THEN Error(242) END;
              IF IsEmpty(paramSeq) THEN Error(248);
              ELSE
                GetFirst(paramSeq,curs,parX);
                IF NOT Ended(curs) THEN Error216(curs) END;
                (*
                 *  now the type transfer "function" is turned
                 *  into a normal call to SYSTEM.CAST with the
                 *  new first parameter a typename desigNode
                 *)
                MakeCast(exp^,id^.typType,parX);  (* set result type *)
              END;
          ELSE Error(246);
          END; (* case *)
        ELSE Error(245);
        END; (* if *)
    | constructorNode, setDesigNode :
	(*
	 *  Here, the calls to nested constructors of anon
	 *  type will have the presumed type passed as input
	 *)
	IF exprType = NIL THEN 
	  BindDesignator(name);
          IF NOT EmptySelList(name) THEN Error(261) END;
          id := name.variable;
          IF id = NIL THEN Error(204);
          ELSIF id^.idClass = typeNode THEN 
	    exprType := id^.typType;
	  ELSE Error(205);
	  END;
	END;
	IF exprType = NIL THEN (* skip *)
	ELSIF exprType^.tyClass = sets THEN SetRangeSeq (exp);
	ELSIF exprType^.tyClass = arrays THEN ArrayRangeSeq(exp);
	ELSIF exprType^.tyClass = records THEN RecordRangeSeq (exp);
        ELSE Error(247);
        END;
    | literalNode : (* nothing, type already known *)
    END;
  END (* WITH exp^ *) ;
  END TraverseExp;

  PROCEDURE StatSeq(seq : Sequence; VAR loopState : LoopStatus);
  (*
   *  Traverse the statement sequence. LoopState indicates whether this 
   *  sequence is (directly or indirectly) within a LOOP statement, and will be 
   *  updated if an EXIT or RETURN is found.
   *)
    VAR crsr : ElemPtr;
        stdc : StatDesc;
	oldS : StatDesc;
	nest : StatDesc;
	tExp : ExprDesc;
        dst  : DStateType;
        val  : SelectAttribute;
        idp  : IdDesc;
	typ, cvTmp : TypeDesc; 
	tmp : StrucTree;
        newLoopState : LoopStatus;      (* for nested LOOPs *)
	compatible : BOOLEAN;
	wrap       : BOOLEAN;
        fInRng, iInRng : BOOLEAN;          (* for FOR loops *)

      PROCEDURE StorageProc(sel : StandardProcs) : IdDesc;
	VAR idPtr : IdDesc;
      BEGIN
       (*
	*   find the currently valid storage allocator
	*)
	IF sel = newP THEN Lookup(allocBkt,idPtr);
	ELSE Lookup(deallBkt,idPtr);
	END;
	IF idPtr = NIL THEN
	  IF sel = newP THEN Error(282) ELSE Error(283) END;
	ELSE CheckValidAllocate(idPtr);
	END;
	RETURN idPtr;
      END StorageProc;

      PROCEDURE Substitute(idP : IdDesc;
                           par : ExprDesc;
                           stm : StatDesc);
	VAR errNo : CARDINAL;
	    par2  : ExprDesc;
      BEGIN
	IF idP <> NIL THEN
	  (*
	   *  make substitute param list
	   * 
	   *  StProcCheck has verified that the first parameter is a variable
	   *  of pointer type; so mark it as a reference parameter 
	   *)
	  par^.actualClass := refActual;
	  CreateExprDesc(par2,literalNode);
	  WITH par2^ DO
	    exprType := crdTyPtr;
	    actualClass := valActual;
	    conValue.fixValue := par^.exprType^.targetType^.size;
	    IF conValue.fixValue = 0 THEN Error(304) END;
	  END;
	  stm^.designator.variable := idP;
	  RecordCallOf(idP);
	  DisposeList(stm^.actualParams);
	  LinkRight(stm^.actualParams,par);
	  LinkRight(stm^.actualParams,par2);
	END;
      END Substitute;

      PROCEDURE StProcCheck(sel : StandardProcs;
                            std : StatDesc);
(* ==================================================================== *
 *      Check calls to standard procedures:
 *
 *        INC (ordinaltype, optionalIncrement);
 *        DEC (ordinalType, optionalDecrement);
 *          if no second parameter, generate one - literal 1;
 *          first parameter must be a variable of ordinal type (VAR parameter);
 *          second assignment compatible with CARDINAL (value parameter).
 *
 *        INCL (setVariable, element);
 *        EXCL (setVariable, element);
 *          first parameter must be a variable of set type (VAR parameter);
 *          second an element of its base type.
 *
 *        UNIXexit (card_expr);
 *	  Assert (bool_expr);
 *
 *	  NEW, DISPOSE
 *	    give warning if more that one param, first param must be
 *	    variable of pointer type, transform into call of allocate
 *	    and create second param of appropriate size
 *
 *        HALT, ABORT;
 *          just check no parameters.
 * ==================================================================== *)

        TYPE  StdProcSet = SET OF StandardProcs;
        VAR curs : ElemPtr;
            firstParam, secondParam, allocParam : ExprDesc;
            endFound   : BOOLEAN;       (* True if INC or DEC 1 etc. *)
	    compatible : BOOLEAN;
	    wrap       : BOOLEAN;
	    stringType : TypeDesc;
        
      BEGIN
        InitCursor(std^.actualParams,curs);
        (* 
	 *    HALT and ABORT first - no parameters 
	 *)
        IF (sel = haltP) OR (sel = abortP) THEN
          IF NOT Ended(curs) THEN Error216(curs); END;
	  IF sel = abortP THEN Warning495(abortP) END;
          RETURN;
        END;
	(*
	 *   All others have at least one param
	 *)
        IF Ended(curs) THEN Error(248); RETURN; END;
        GetNext(curs,firstParam);
        Assert(firstParam <> NIL);
	(*
	 *   Assert, variable number of params
	 *)
	IF sel = assertP THEN
	  IF Ended(curs) THEN
	    CheckActualParamList(wrap, std^.actualParams,oldAssertFrms);
	  ELSE
            CheckActualParamList(wrap, std^.actualParams,newAssertFrms);
	  END;
	  RETURN;
	END;
	(*
	 *   Traverse first param on the rest ...
	 *)
	TraverseExp(firstParam);

	IF firstParam^.exprType = NIL THEN RETURN END;

	(* 
	 *  now peel off the exitP case 
	 *)
        IF sel = exitP THEN
          IF NOT Ended(curs) THEN Error216(curs) END;
	  CheckedAssignCompatible(firstParam,crdTyPtr,compatible);
 	  IF NOT compatible THEN Error(214) END;
          RETURN;
	END;

        (* Others have two parameters - first is VAR *)
        IF NOT IsVariable(firstParam) THEN Error(255); END;

	endFound := Ended(curs);
        IF NOT endFound THEN GetNext(curs,secondParam) END;

        (* Now procedure-specific checks *)
        CASE sel OF
        | decP,
          incP  :
            IF NOT IsOrdinalType(firstParam^.exprType) THEN Error(206); END;
	    IF IsFORThreat (firstParam^.name.variable) THEN Error(279) END;
	    IF NOT (firstParam^.exprType^.tyClass IN
		    TyClassSet{subranges,chars,enums}) THEN
	      EXCL(firstParam^.testFlags,rangeTests);
	    END;
	   (*
	    *   inc and dec are no longer included in varParThreat
	    *	since such a usage does not prevent the variable 
	    *	from having a register allocation.  M2LazyCopy 
	    *   takes inc and dec into account directly through
	    *   the medium of the "suspect procs" set. (kjg Jan-93)
	    *
	    *   firstParam^.name.variable^.varParThreat := TRUE;
	    *)
	    IF AccessModeOf(firstParam^.name) IN anyUplevel THEN
	      INCL(firstParam^.name.variable^.varUseSet,uplevThr);
            END;
	    IF endFound THEN
	      CreateExprDesc(secondParam,literalNode);
	      WITH secondParam^ DO
		exprType := crdTyPtr;
		actualClass := valActual;
		conValue.fixValue := 1;
	      END;
	      LinkRight (std^.actualParams, secondParam);
            ELSE
	      TraverseExp(secondParam);
	      IF IsSignedType(firstParam^.exprType) THEN
		CheckedAssignCompatible(secondParam,intTyPtr,compatible);
	      ELSE CheckedAssignCompatible(secondParam,crdTyPtr,compatible);
	      END;
	      IF NOT compatible THEN Error(253) END;
	    END;
	| exclP, inclP :
	    IF endFound THEN Error(248); RETURN END;
            IF firstParam^.exprType^.tyClass<>sets
              THEN ExpErr (firstParam,275);
            ELSE
	 (*
	  *   see the note on inc and dec, above ...
	  *
	  *   firstParam^.name.variable^.varParThreat := TRUE;
	  *)
	      TraverseExp(secondParam);
	 (*
	  *   Of course, we want _Assign_Compatability here!
	  *)
	      CheckedAssignCompatible(secondParam,
		      firstParam^.exprType^.baseType, compatible);
	      IF NOT compatible THEN Error(253) END;
            END;
(* -- for historical compatibility -- *)
	| shiftP, rotateP :
	    Warning495(sel);
	    IF firstParam^.exprType <> setTyPtr THEN Error(214) END;
	    IF endFound THEN Error(248); RETURN END;
	    INCL(firstParam^.name.variable^.varUseSet,varParThr);
	    TraverseExp(secondParam);
	    IF  (sel = rotateP) AND
		(secondParam^.exprClass = literalNode) THEN
	      secondParam^.conValue.fixValue := 
			secondParam^.conValue.fixValue MOD bitsInWord;
	    END;
	    CheckedAssignCompatible(secondParam,intTyPtr,compatible);
	    IF NOT compatible THEN Error(253) END;
(* -- cut here -- *)
        | newP,
	  disP :
	    IF firstParam^.exprType^.tyClass = pointers THEN
	      IF NOT endFound THEN
	        lastPos := secondParam^.sourceLoc;
	        Error(499); (* tags are ignored *)
	        WHILE NOT Ended(curs) DO GetNext(curs,secondParam) END;
	      END;
	      Substitute(StorageProc(sel),firstParam,std);
	    ELSIF firstParam^.exprType^.tyClass = stringTs THEN (* #### *)
	     (*
	      *  For dynamic strings we do not substitute
	      *  the visible ALLOCATE etc, but expand in
	      *  M2ObjectCode, using extra param added on.
	      *)
	      IF sel = newP THEN
	        IF endFound THEN Error(248); RETURN END;
	        TraverseExp(secondParam);
		CheckedAssignCompatible(secondParam,intTyPtr,compatible);
		IF NOT compatible THEN Error(253) END;
                endFound := Ended(curs);
	      END; 
	      IF NOT endFound THEN
	        IF NOT Ended(curs) THEN Error216(curs) ELSE Error(216) END;
	      END;
	     (* BEWARE: this creates a heterogeneous list! *)
	      CreateExprDesc(allocParam,desigNode);
	      allocParam^.name.variable := StorageProc(sel);
	      LinkRight(std^.actualParams, allocParam); 
	    ELSE
	      LoadGlobals(firstParam^.exprType,adrTyPtr);
	      Error(294); RETURN; (*! an unique message later *)
	    END;
	    INCL(firstParam^.name.variable^.varUseSet,varParThr);
	| appendP :
	    IF firstParam^.exprType^.tyClass = stringTs THEN (* #### *)
	      TraverseExp(secondParam);
	      IF (secondParam = NIL) OR
		 (secondParam^.exprType = NIL) THEN RETURN END;
	      stringType := firstParam^.exprType^.targetType;
	      IF (secondParam^.exprType^.tyClass = stringTs) AND 
		 (secondParam^.exprType^.targetType = stringType) THEN
		std^.appendClass := 0;
	      ELSIF (secondParam^.exprType^.tyClass = arrays) AND 
		    (secondParam^.exprType^.elementType = stringType) THEN
		std^.appendClass := 1;
	      ELSIF (stringType = secondParam^.exprType) OR
		    (Compatible(stringType,secondParam^.exprType) AND
		     TypesOverlap(stringType,secondParam^.exprType)) THEN
		std^.appendClass := 2;
	      ELSE
		Error(332); (* bad second paramter for APPEND *)
	      END;
	      CreateExprDesc(allocParam,desigNode);
	      allocParam^.name.variable := StorageProc(newP);
	      LinkRight(std^.actualParams, allocParam); 
	      CreateExprDesc(allocParam,desigNode);
	      allocParam^.name.variable := StorageProc(disP);
	      LinkRight(std^.actualParams, allocParam); 
	    ELSE
	      Error(330); (* first param must be of STRING type *)
	    END;
	| resetP :
	    IF firstParam^.exprType^.tyClass = stringTs THEN (* #### *)
	      TraverseExp(secondParam);
	      IF (secondParam^.exprType <> NIL) AND
	          NOT Compatible(secondParam^.exprType, intTyPtr) THEN
		Error(333); (* bad second paramter for RESET *)
	      END;
	    ELSE
	      Error(330); (* first param must be of STRING type *)
	    END;
	| concatP :
	    IF  (firstParam^.exprType^.tyClass = stringTs) AND
		(firstParam^.exprType^.targetType = chTyPtr) THEN
	      TraverseExp(secondParam);
	      IF (secondParam = NIL) OR
		 (secondParam^.exprType = NIL) THEN RETURN END;
	      IF (secondParam^.exprType^.tyClass = S1) OR
		 (secondParam^.exprType^.tyClass = SS) OR
		 (secondParam^.exprType^.tyClass = stringTs) AND
			(secondParam^.exprType^.targetType = chTyPtr) OR
		 (secondParam^.exprType^.tyClass = arrays) AND
			(secondParam^.exprType^.elementType = chTyPtr) OR
		        (WidenedType(secondParam^.exprType) = chTyPtr) THEN
	        CreateExprDesc(allocParam,desigNode);
	        allocParam^.name.variable := StorageProc(newP);
	        LinkRight(std^.actualParams, allocParam); 
	        CreateExprDesc(allocParam,desigNode);
	        allocParam^.name.variable := StorageProc(disP);
	        LinkRight(std^.actualParams, allocParam); 
                IF current^.body^.maxParSize <= oP5 THEN 
                  current^.body^.maxParSize := oP5 + INT(bytesInWord);
                END;      
	      ELSE
		Error(331); (* p2 must be STRING or ARRAY of CHAR, or CHAR *)
	      END;
	    ELSE
	      Error(330); (* first param must be of STRING type *)
	    END;
     (* | haltP : Special case above ; *)
        END;
        IF NOT endFound AND NOT Ended(curs) THEN Error216(curs) END;
      END StProcCheck;

    PROCEDURE BranchScan(seq : Sequence);
      VAR ifCurs : ElemPtr;  ifDesc : IfDesc;
    BEGIN
      InitCursor(seq,ifCurs);
      WHILE NOT Ended(ifCurs) DO
        GetNext(ifCurs,ifDesc);
        IF ifDesc^.condition <> NIL THEN
          TraverseExp(ifDesc^.condition);
          IF ifDesc^.condition^.exprType <> NIL THEN
            IF GetTyClass(ifDesc^.condition) <> bools THEN Error (221);
(* !
 *          ELSE
 *            IF ifDesc^.condition^.exprClass = literalNode THEN
 *              Remove dead code? But we only have one branch here ...
 *              IF ifDesc^.condition^.conValue.fixValue = ORD(TRUE) THEN
 *              .....
 *              END;
 *            END;
 *)
            END;
          END;
        END;
        StatSeq(ifDesc^.statSeq,loopState);
      END;
    END BranchScan;

    PROCEDURE CaseScan(seq : Sequence);
      VAR casCurs : ElemPtr;  casDesc : CaseDesc;
    BEGIN
      InitCursor(seq,casCurs);
      WHILE NOT Ended(casCurs) DO
        (* case ranges are bound during parsing *)
        GetNext(casCurs,casDesc);
        StatSeq(casDesc^.statSeq,loopState);
      END;
    END CaseScan;

    PROCEDURE UnLinkLeft(VAR seq : Sequence);
    (*
     *  Remove the leftmost element of seq.
     *  Currently uses GenSequence primitives to copy all but one to a
     *  new sequence; move to GenSequence?
     *)
      VAR newSeq : Sequence;
          curs : ElemPtr;
          element : ADDRESS;
    BEGIN
      Assert(NOT IsEmpty(seq));
      InitSequence(newSeq);
      GetFirst(seq,curs,element);
      WHILE NOT Ended(curs) DO
        GetNext(curs,element);
        LinkRight(newSeq,element);
      END;
      DisposeList(seq);
      seq := newSeq;
    END UnLinkLeft;

      PROCEDURE Highest(exp : ExprDesc) : CARDINAL;
        (*
	 *  this procedure return the highest possible
	 *  value of the expression, cast to cardinal
	 *)
      BEGIN
	IF exp^.exprClass <> literalNode THEN
	  RETURN MaxOfOrdType(exp^.exprType);
	ELSIF Compatible(exp^.exprType,chTyPtr) THEN
	  RETURN ORD(exp^.conValue.charValue);
	ELSE RETURN exp^.conValue.fixValue;
	END;
      END Highest;

      PROCEDURE Lowest(exp : ExprDesc) : CARDINAL;
        (*
	 *  this procedure return the lowest possible
	 *  value of the expression, cast to cardinal
	 *)
      BEGIN
	IF exp^.exprClass <> literalNode THEN
	  RETURN MinOfOrdType(exp^.exprType);
	ELSIF Compatible(exp^.exprType,chTyPtr) THEN
	  RETURN ORD(exp^.conValue.charValue);
	ELSE RETURN exp^.conValue.fixValue;
	END;
      END Lowest;

  BEGIN (* StatSeq *)
    InitCursor(seq,crsr);
    WHILE NOT Ended(crsr) DO
      GetNext(crsr,stdc);
      WITH stdc^ DO
        lastPos := sourceLoc;
        CASE statClass OF
	| emptyNode  : (* nothing *)
        | assignNode : (* check : desig, expr, assign-compat *)
            BindDesignator(designator);
	   (*
	    *  If this occurrence includes a dereference, this 
	    *  is a _use_ of the designator, otherwise it is
	    *  a definition of the designator.
	    *)
	    IF AccessModeOf(designator) IN anyUplevel THEN
	      INCL(designator.variable^.varUseSet,uplevThr);
            END;
            TraverseExp(expression);
            lastPos := sourceLoc;
            IF designator.variable = NIL THEN Error(204);
            ELSIF designator.variable^.idClass <> varNode THEN Error(235);
            ELSE
              (* threat to FOR control variable? *)
              IF IsFORThreat(designator.variable) THEN Error(279) END;
              (* now check assign compat *)
              GetDesigType(designator,typ);
	      desigType := typ;
              CheckedAssignCompatible(expression,typ,compatible);
	      IF NOT compatible THEN 
		(*
		 *  specific message for open arrays
		 *)
	        IF UnivConform(expression^.exprType,typ) THEN
		  IF verbose IN modState THEN Error(494) ELSE Warning494 END;
	        ELSIF (typ^.tyClass = arrays) AND typ^.isDynamic THEN
		  Error(319);
		ELSE Error(258);
		END;
	      END;
          (*
           *  assert: expression <> NIL else parse error, however ...
           *          semantically bad expression ==> exprType = NIL;
           *          literalNodes cannot be bad
           *)
              IF typ <> NIL THEN
                IF (typ^.tyClass = arrays) AND
                   (expression^.exprType <> NIL) AND
                   (expression^.exprType^.tyClass = S1) THEN 
                  expression^.exprType := PointerTo(SS); (* coerce to string *)
                END;
              END;
            END;
        | procCallNode : (* check : desig, params *)
            BindDesignator(designator);
	    wrap := FALSE;
            idp := designator.variable;
            IF idp = NIL THEN Error(204);
            ELSE
              IF idp^.idClass = stProc THEN
                StProcCheck(idp^.procVal,stdc);
		(* temporary during period of grace ... *)
	      ELSIF (idp^.idClass = stFunc) AND
		  ((idp^.procVal = rotateP) OR (idp^.procVal = shiftP)) THEN
                StProcCheck(idp^.procVal,stdc);
              ELSIF idp^.idClass IN
                      IdClassSet{procNode,procHeader,externProc} THEN
                RecordCallOf(idp);
                IF NOT EmptySelList(designator) THEN Error(243) END;
                (* is it a proper procedure? *)
		typ := idp^.procType;
	        IF typ^.tyClass = procTypes THEN 
		  (* check params against formals *) 
		  IF (typ^.parentMod^.idClass = exportNode) AND 
		      typ^.parentMod^.direct THEN 
		    CheckDirectParamList(actualParams, typ^.params)
		  ELSE
                    CheckActualParamList(wrap,actualParams,typ^.params);
		    IF wrap THEN 
                      IF emitCil IN modState THEN
		        M2CilWrappers.MkWrap
                                         (designator,actualParams,typ,current);
                      ELSE
		        M2DcfWrappers.MkWrap
                                         (designator,actualParams,typ,current);
                      END;
                    END;
		  END;

		  IF typ^.preCon <> NIL THEN 
		   (*
		    *   We pass in the actual parameter sequence, and 
		    *   the precondition expression from the TypeDesc.  
		    *   We get back the initialisation statement seq, 
		    *   and the (possibly modified) actual parameters.  
		    *) 
		    CreateStatDesc(oldS,emptyNode); 
		    CreateStatDesc(nest,compoundNode); 
		    callPos := sourceLoc;
		    CheckPrecon(actualParams,typ^.preCon,nest^.inlineBody); 
		    LinkRight(nest^.inlineBody,oldS); (* copy new to end  *)
		    oldS^ := stdc^;		(* overwrite the new stat *)
		    stdc^ := nest^;		(* overwrite the old stat *)
		  END; 

                ELSE Error(249);
                END
              ELSIF (idp^.idClass = varNode) OR
                    (idp^.idClass = constNode) THEN	(* kjg Nov 92 *)
                IF idp^.idClass = varNode THEN
                  GetDesigType(designator,typ);
                ELSE (* idp^.idClass = constNode *)
                  GetConstDesig(designator,typ);
		END;
                IF  typ <> NIL THEN
		  IF typ^.parSiz = infinity THEN
		    typ^.parSiz := FormalSize(typ);
		  END;
						 (* fixed kjg 23-Mar-93 *)
		  IF typ^.parSiz > current^.body^.maxParSize THEN
	            current^.body^.maxParSize := typ^.parSiz;
		  END;
                  IF typ^.tyClass = procTypes THEN
                    (* check params against formals *)
		    IF (typ^.parentMod^.idClass = exportNode) AND
		        typ^.parentMod^.direct THEN
                      CheckDirectParamList (actualParams, typ^.params)
		    ELSE
                      CheckActualParamList(wrap, actualParams, typ^.params);
		      IF wrap THEN 
                        IF emitCil IN modState THEN 
                          M2CilWrappers.MkWrap
                                        (designator,actualParams,typ,current);
                        ELSE
		          M2DcfWrappers.MkWrap
                                        (designator,actualParams,typ,current);
                        END;
                      END;
		    END;

		    IF typ^.preCon <> NIL THEN 
		     (*
		      *   We pass in the actual parameter sequence, and 
		      *   the precondition expression from the TypeDesc.  
		      *   We get back the initialisation statement seq, 
		      *   and the (possibly modified) actual parameters.  
		      *) 
		      CreateStatDesc(oldS,emptyNode); 
		      oldS^ := stdc^;		(* overwrite new with old  *)
		      CreateStatDesc(nest,compoundNode); 
		      callPos := sourceLoc;
		      CheckPrecon(actualParams,typ^.preCon,nest^.inlineBody); 
		      LinkRight(nest^.inlineBody,oldS);	(* copy old to end *)
		      stdc^ := nest^;		(* overwrite the old stat  *)
		    END; 

                  ELSE Error(250);
                  END;
                (* else error already notified by GetDesigType *)
		END;
              ELSE Error(249);
              END;
            END;
        | caseNode   :
            TraverseExp(caseInfo^.switch);
            IF caseInfo^.switch^.exprType <> NIL THEN
              FindMinAndMax(caseInfo,cases);
            END;
            CaseScan(cases);
            StatSeq(default,loopState);
        | ifNode     : BranchScan(branches)
        | whileNode  :
            TraverseExp(condition);
            IF condition^.exprType <> NIL THEN
              IF GetTyClass(condition) <> bools THEN Error (221);
         (* ! ELSE Check for dead code cf BranchScan? *)
              END;
            END;
            StatSeq(wrBody,loopState);
        | repeatNode :
            StatSeq(wrBody,loopState);
            TraverseExp(condition);
            IF condition^.exprType <> NIL THEN
              IF GetTyClass(condition) <> bools THEN Error (221);
         (* ! ELSE Check for dead code cf BranchScan? *)
              END;
            END;
        | loopNode   :
            newLoopState := noExitYet;
            StatSeq(loopBody, newLoopState);
            CASE newLoopState OF
            | notInLoop : Assert (FALSE);
            | noExitYet : lastPos := sourceLoc; Error (508);
            | exited    : (* normal case - do nothing *) ;
            | returned  : loopState := returned;
            END;
        | forNode    :
	    IF  (controlVariable <> NIL) AND
		(uplevThr IN controlVariable^.varUseSet) THEN
	      Error(296); (* control variable is uplevel addressed *)
	    END;
            IF IsFORThreat(controlVariable) THEN Error(279) END;
 	   (* 
 	    *  M2Parser has determined that controlVariable is local
 	    *  but may have since been obscured by a WITH fieldname.
 	    *)
 	    IF WithBinding(controlVariable^.name) <> NIL THEN Error(326) END;
           (* 
	    *  Check initial and final value expressions for internal
            *  correctness and for compatibility with the control variable;
            *  Parser.ForStatement has already checked the constant step
	    *)
	    typ := controlVariable^.varType;
            TraverseExp(initial);
	   (*
	    *	assert: (controlVariable <> NIL) AND
            *                  (controlVariable^.idClass = varNode);
	    *	otherwise, Parser.ForStatement has reported errors
	    *)
            CheckedAssignCompatible(initial, typ, compatible);
	    IF NOT compatible THEN Error(258); END;
            TraverseExp(final);
	    IF NOT Compatible(final^.exprType, typ) THEN Error(324) END;
	   (*
	    *  Crude but effective ...
	    *)
	    fInRng := TypesOverlap(typ,final^.exprType)  OR
		       ((final^.exprClass = literalNode) AND
			  LiteralInRange(typ,final^));
	    iInRng := TypesOverlap(typ,initial^.exprType)  OR
		       ((initial^.exprClass = literalNode) AND
			  LiteralInRange(typ,initial^));

	    IF fInRng THEN EXCL(final^.testFlags,rangeTests) END;

            IF controlVariable <> NIL THEN
              LinkLeft(activeControls,controlVariable);
            END;
	    (*
	     *   the following code creates a temporary subrange type which 
	     *   is used as the type within the FOR loop. This may lead
	     *   to the elimination of redundant index tests in some cases
	     *)

	    IF (initial <> NIL) AND (final <> NIL) THEN
	        (* always make temp type *)
	        CreateTypeDesc(thisCompileUnit, cvTmp, subranges);
		IF (initial^.exprClass <> literalNode) OR
		   (final^.exprClass <> literalNode) THEN
		 (*
		  *  the so-called "hard" case
		  *)
		  MakeNewCurrent(cards,countDownVar);
		END;
	       (*
		*  If the final value is a designator, then
		*  just remember it.  If it turn out that there
		*  are accesses to open arrays, M2ObjectCode 
		*  will check whether it is the correct HIGH
		*)
		IF final^.exprClass = desigNode THEN
		  cvTmp^.hiDesc := final^.name.variable;
		END;
	        WITH cvTmp^ DO
	          IF typ^.tyClass <> subranges THEN hostType := typ
	          ELSE hostType := typ^.hostType;
	          END;
	          size := typ^.size;	(* in cases of subranges of subranges *)
					(* size is size of actual var. Oct-90 *)
	          alignMask := hostType^.alignMask;
	          (*
	           *  Now to extract the extremal values
		   *
		   *  This is not exactly straighforward, since
		   *  the initial expression may be not be 
		   *  compatible with the control variable type.
		   *  If compatible, then use value, else use
		   *  the extremal value of the cv type (typ).
		   *  In any case, final is always compatible.
	           *)
	          IF stepSize > 0 THEN
		    IF iInRng THEN 
		      minRange := Lowest(initial); 
		    ELSE 
		      minRange := MinOfOrdType(typ); 
		    END;
		    IF fInRng THEN 
		      maxRange := Highest(final);
		    ELSE 
		      maxRange := MaxOfOrdType(typ);
		    END;
	          ELSE 
		    IF iInRng THEN 
		      maxRange := Highest(initial); 
		    ELSE 
		      maxRange := MaxOfOrdType(typ); 
		    END;
		    IF fInRng THEN
		      minRange := Lowest(final);
		    ELSE
		      minRange := MinOfOrdType(typ);
		    END;
	          END;
	       (* 
		* StdError.WriteCard(minRange,15);
		* StdError.WriteCard(maxRange,15);
		* StdError.WriteCard(MinOfOrdType(typ),15);
		* StdError.WriteCard(MaxOfOrdType(typ),15);
		* StdError.WriteLn;
		*)
	        END;
	        controlVariable^.varType := cvTmp;
	    END;

            StatSeq(forBody,loopState);

	    controlVariable^.varType := typ;
	    (*
	     *  restore cv type.
	     *  Don't dispose cvTmp^ as it may now be the 
	     *  exprType of expressions in the statSeq
	     *)

            IF controlVariable <> NIL THEN
              UnLinkLeft(activeControls);
            END;
        | withNode   :
            BindDesignator(withInfo^.desig);
            EnterWith(withInfo); (* & notify errors *)
            StatSeq(withBody,loopState);
            ExitWith;
        | exitNode   :
            CASE loopState OF
            | notInLoop : Error (278);
            | noExitYet : loopState := exited;
            | exited    : (* second exit *) ;
            | returned  : (* don't downgrade to exited *) ;
            END;
        | retryNode  :
            IF exceptState <> inExcept THEN Error(321) END;
        | returnNode :
            IF  (current^.idClass <> modNode) AND
                (current^.procType^.tyClass = funcTypes) THEN
              IF returnResult = NIL THEN Error(251);
              ELSE
		destTypeDesc := current^.procType^.result;
                TraverseExp(returnResult);
                (* check assign compatibility of result *)
                CheckedAssignCompatible(returnResult, 
                                        destTypeDesc,
					compatible);
		IF NOT compatible THEN
                  lastPos := stdc^.sourceLoc; Error(259);
		END;
              END;
            ELSIF returnResult <> NIL THEN Error(252);
            END;
            loopState := returned;
        END;
      END;
    END;
  END StatSeq;

  PROCEDURE CheckBlock(thisProc : IdDesc);
    VAR blockNotInLoop : LoopStatus;
  BEGIN
    Assert(thisProc^.body <> NIL);
    SetCurrentScope(thisProc);
    WITH thisProc^.body^ DO
      IF NOT (IsEmpty(exceptSeq) AND IsEmpty(finalExSeq)) THEN
        INCL(callAttrib,hasExcept);
        exceptState := inNormal;
      ELSE
        exceptState := noExcept;
      END;
      blockNotInLoop := notInLoop;
      StatSeq(statements,blockNotInLoop);
      blockNotInLoop := notInLoop;
      StatSeq(finalSeq,blockNotInLoop);
      IF exceptState = inNormal THEN
        exceptState := inExcept;
        blockNotInLoop := notInLoop;
        StatSeq(exceptSeq,blockNotInLoop);
        blockNotInLoop := notInLoop;
        StatSeq(finalExSeq,blockNotInLoop);
      END;
    END;
  END CheckBlock;


  PROCEDURE InitPointers;
  BEGIN
    (*
     *  castPtr must be bound to the system stdFunc,
     *  even if "CAST" is not imported or is occluded
     *)
    castPtr := CastIdDesc();
    chTyPtr := PointerTo(chars);
    setTyPtr := PointerTo(sets);
    crdTyPtr := PointerTo(cards);
    intTyPtr := PointerTo(ints);
    adrTyPtr := PointerTo(adrs);
    boolTyPtr := PointerTo(bools);
    rrTyPtr  := PointerTo(RR);
    fltTyPtr := PointerTo(floats);
    dblTyPtr := PointerTo(doubles);
    hugeTyPtr := PointerTo(hInts);
    (* formal param list for lengthP *)
    InitSequence(lengthFormals);
    InitSequence(oldAssertFrms);
    LinkLeft(lengthFormals,MakeFormal(chTyPtr,anonBkt,anonBkt,openValForm,1));
    (* formal param list for assertP *)
    newAssertFrms := lengthFormals;	(* sharing the nodes ! *)
    LinkLeft(newAssertFrms,MakeFormal(boolTyPtr,anonBkt,anonBkt,valForm,0));
    LinkLeft(oldAssertFrms,MakeFormal(boolTyPtr,anonBkt,anonBkt,valForm,0));
  END InitPointers;

  PROCEDURE SemanticCheck;
    VAR thIx : INTEGER;
	thId : IdDesc;

   (* Check if any nested module has an exception handler *)
    PROCEDURE CheckExcept(str : IdString) : BOOLEAN;
      VAR idx : INTEGER;
    BEGIN
      FOR idx := 0 TO HIGH(str) DO
        WITH str[idx]^ DO
	  IF idClass = modNode THEN 
	    RETURN (hasExcept IN body^.callAttrib) OR CheckExcept(body^.nestBlks);
	  END;
        END;
      END;
      RETURN FALSE;
    END CheckExcept;

VAR blkList : IdString;
  BEGIN
blkList := codeBlkList;
    FOR thIx := 0 TO HIGH(codeBlkList) DO
      thId := codeBlkList[thIx];
      CheckBlock(thId);
     (*
      * all handlers for a procedure use the same descriptor
      * check if any nested module needs an exception descriptor
      * (nested modules will have already been passed to CheckBlock)
      *)
      IF thId^.idClass = procNode THEN
	WITH thId^.body^ DO
          IF (hasExcept IN callAttrib) OR CheckExcept(nestBlks) THEN
            MakeNewCurrent(adrs,exceptDesc);
            INCL(exceptDesc^.varUseSet,exceptionDescriptor);
            INCL(exceptDesc^.varUseSet,varParThr);
          END;
        END;
      END;
     (*
      *  this next call ensures that correct parameter
      *  sizes are set, for exported procedures which
      *  are not otherwise referenced (kjg) Apr-90
      *)
      IF thId^.procType^.parSiz = infinity THEN
	thId^.procType^.parSiz := FormalSize(thId^.procType);
      END;
    END;
    CheckBlock(thisCompileUnit);
    WITH thisCompileUnit^.body^ DO
      IF (hasExcept IN callAttrib) OR CheckExcept(nestBlks) THEN
        MakeNewCurrent(adrs,exceptDesc);
        INCL(exceptDesc^.varUseSet,exceptionDescriptor);
        INCL(exceptDesc^.varUseSet,varParThr);
      END;
    END;
  END SemanticCheck;

BEGIN
  currentWith := NIL;
  InitSequence(activeControls);
END M2Traversal.
