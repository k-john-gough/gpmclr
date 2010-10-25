(****************************************************************)
(*                                                              *)
(*     LITTLE-ENDIAN VERSION FOR DECSTATION. JAN 90 (kjg)	*)
(*	     NATIVE CODE VERSION FEBRUARY 1990 (kjg)		*)
(*	LITTLE-ENDIAN D-CODE VERSION AUGUST 1990 (kjg)		*)
(*       GENERIC D-CODE VERSION (Tuebingen) JANUARY 1992	*)
(*                                                              *)
(****************************************************************)

(****************************************************************)
(*                                                              *)
(*              Modula-2 Compiler Source Module                 *)
(*                                                              *)
(*          Tree Traversal and ObjectCode Production            *)
(*                                                              *)
(*      (c) copyright 1988 Faculty of Information Technology    *)
(*                                                              *)
(*      original module : kjg May 1988                          *)
(*      modifications   : bigEndian lit-code selected 03-Dec-88 *)
(*                      : Case selector traps         27-Feb-89 *)
(*			: soap implementation started 07-Mar-89 *)
(*			: uplevel high access fixed   08-Mar-89 *)
(*			: record and array literals   20-Nov-89 *)
(*			: IRIS mods moved back to HP  30-Nov-89 *)
(*			: fix char fors with ul 377C  14-Jan-90 *)
(*			: order of stack for assign		*)
(*			: has been switched 	      21-Aug-90 *)
(*			: function return values      20-Oct-90 *)
(*                      : mv defLab alloc. in En'Case  1-Nov-90 *)
(*			: address adds fixed 	      28-Dec-90 *)
(*                      : functions returning records    Jan-91 *)
(*                      : object code output             Feb-91 *)
(*			: CHAR array indexes          03-Jun-91 *)
(*			: floating point ops	      20-Jun-91 *)
(*                      : dump proc names for debug      Aug-91 *)
(*			: correction of BuildBigSet      Sep-91 *)
(*			: functions returning arrays     Oct-92 *)
(*			: runtime rec, arr constructors  Oct-92 *)
(*			: callee copy value records	 Oct-92 *)
(*			: fix relops with lhs literal    Jan-93 *)
(*								*)
(*   =============== merged mips and i386 source ============	*)
(*			   kjg 22 Mar 93			*)
(*                                                              *)
(*			: fix code for incAdr,decAdr  30-Mar-93 *)
(*                                                              *)
(****************************************************************
$Log: m2object.mod,v $
Revision 1.43  1997/01/16 04:45:10  gough
        new code for CASE statements, plus many other detailed changes.
        Code for testing preconditions also added.

Revision 1.42  1996/11/27 02:21:59  lederman
replace OuputBlock() & OutputBody() with multiple recursions over the nestBlks
structure - EmitProcs, EmitMods, EmitModExcepts

Revision 1.41  1996/09/20 08:05:48  lederman
pick up appendClass from StatDesc

Revision 1.40  1996/09/19 08:06:47  lederman
fixes for APPEND now using the second params appendClass to classify correctly
also fix StringIndexCheck to check the integer (not cardinal) range [-1 .. n]

Revision 1.39  1996/08/30 00:46:52  lederman
removed some extraneous ofst's ...

Revision 1.38  1996/08/28 23:02:07  gough
1. when passing open arrays to APPEND,CONCAT compute elemNum from HIGH
2. scale HIGH when passing strings to amorphous open arrays

Revision 1.37  1996/08/15 03:53:42  gough
fix to stringTs passed as VAR params

Revision 1.36  1996/08/07 23:43:07  gough
code for VARSTRS.CUT
also second param to VariableCheck becomes INTEGER rather than CARDINAL

Revision 1.35  1996/08/06 23:42:28  gough
generating code for passing strings to value open arrays using wrappers

Revision 1.34  1996/07/29 23:59:18  gough
produce inline code for string appends and concats, and indexing
into generic string types.

Revision 1.33  1996/05/10 06:55:42  lederman
make all param. offsets INTEGER to handle huge value records

Revision 1.32  1996/01/08 05:30:30  gough
many changes: use hiDesc to eliminate some tests in open arrays,
	track variables and emit alias info for optimiser

Revision 1.31  1995/12/05 23:26:40  lederman
mergId -> notOp^.mergId in notNode case

Revision 1.30  1995/10/25 01:11:29  lederman
MakeWord use overflow rather than range tests everywhere

Revision 1.29  1995/10/20 04:46:01  lederman
check both left & right expr. of HUGE relops in case either is literal

Revision 1.28  1995/10/10 23:32:05  lederman
DCode V3 HugeInt support stuff

Revision 1.27  1995/09/15 07:50:11  gough
Completely eliminate the use of pshFi and popFi in PushBool and FOR loops

# Revision 1.26  1995/09/06 07:31:37  gough
# fix missing selConstNode case in BoolJump()
#
# Revision 1.25  1995/03/23  23:00:43  gough
# numerous changes related to multi-dimensional open arrays
#
# Revision 1.24  1995/03/17  05:00:45  gough
# must use _actual_ size and alignment in computation of outgoing HIGH
# for openMarshallNodes.  In and out sizes are not the same size with WORD,HIGH
#
# Revision 1.22  1995/03/14  01:43:48  gough
# Marshalling of value open array parameters on the caller side
#
# Revision 1.21  1995/03/02  08:51:19  gough
# encoding new castNode node type
#
# Revision 1.20  1995/02/20  02:54:45  gough
# fixed deref of cast objects to use narrower of the two types with an
# appropriate sign or zero extension.
#
# Revision 1.19  1995/01/09  02:52:04  gough
# Install better code for inNode evaluation, and fix up check so that
# the out-of-range index check is based on the leftOp of the inNode,
# since this is the ExprDesc which M2Traversal modifies
#
# Revision 1.18  1995/01/06  03:36:25  gough
# remove import of jumpTabElSize
#
# Revision 1.17  1995/01/05  05:40:06  gough
# two things:
# 	fix up casts to take smaller of two sizes in Deref, except for reals
# 	change emission of CASE jump to use "switch", not "jump"
#
# Revision 1.16  1994/11/11  01:41:04  gough
# stop case statement selector statements being reevaluated in trap...
#
# Revision 1.15  1994/10/18  07:31:43  gough
# fix up comment for producing RngAsserts
#
# Revision 1.14  1994/10/12  05:58:09  lederman
# just change parBytes to Int16 to match parameter types
#
# Revision 1.13  1994/10/12  05:00:47  gough
# put in initial code for range assertions using RngAssert
#
# Revision 1.12  1994/10/11  07:18:00  gough
# tidy up use of sunStructs
#
# Revision 1.11  1994/10/10  05:14:03  gough
# changes for writing out value mode records with sunStructs flag
#
# Revision 1.10  1994/09/19  07:13:32  lederman
# allow jumpTabElSize to be smaller than wordSize
#
# Revision 1.9  1994/09/05  02:45:06  gough
#  Fix semantics of inNode's to conform to ISO DIS. Note that the rangeTest
#  flag has modified semantics, and does a FALSE test, and not a trap.
#
# Revision 1.8  1994/08/10  00:48:18  gough
# keep case statement selector expression in a temporary in order
# to avoid leaving values on shadow stack in the interpreter versions
#
# Revision 1.7  1994/08/09  07:49:23  gough
# serialize parameters for setRngIncl
#
# Revision 1.6  1994/07/15  04:13:18  lederman
# optimisation for 0.0 ==> pshZ; iToDbl / iToFlt;
#
# Revision 1.5  1994/07/01  05:16:53  lederman
# fix 32-bit dependancies - do big set offsets with Div & Mul now
# change pushing literal floats to deref of constant
#
# Revision 1.4  1994/06/07  07:04:45  gough
# call of new procedure NegateBool
#
# Revision 1.3  1994/05/25  02:04:05  gough
# new form FOR loops, with literal bound, removing the unconditional
# jump on the back edge in all cases, and the second counter in const cases.
#
# Revision 1.2  1994/04/21  06:28:20  lederman
#  Fix LocalInfo() to get BigEndian literal sets the right way around
#
# Revision 1.1  1994/04/07  05:08:00  lederman
# Initial revision
*****************************************************************
Revision 1.23  94/02/20  12:00:59  gough
tidy up range tests in extended VAL code generation

Revision 1.22  94/02/17  08:27:33  gough
fix up extended val, int, rotate, shift, entier, round
make abs and negate etc. use optional mode markers

Revision 1.21  94/02/02  13:29:59  gough
make order of mkPars for inline asserts stackparam/fixedassembly indep.

Revision 1.20  93/11/18  17:29:11  gough
*** empty log message ***

Revision 1.19  93/11/18  13:31:59  gough
unwind first element of loop for word set constructor,
also put dec on loop count of for loop last of all (see comment)

Revision 1.18  93/11/16  08:37:10  gough
retcut support

Revision 1.17  93/11/11  09:23:03  gough
fix up push of single word set constants

Revision 1.16  93/10/11  13:39:58  gough
clean up of previous mod, move extraction of tmp offsets inside guard

Revision 1.15  93/10/08  13:54:31  gough
complete revision of for loop encoding. Using computed count.

Revision 1.14  93/10/06  12:00:34  gough
fix up for loop upper bound checks finally (whimper, whimper)

Revision 1.13  93/09/10  17:55:55  gough
clean up case statement code which needed (* $T- *) etc.

Revision 1.12  93/08/13  17:53:59  gough
test flags on "VAL" is on _second_ parameter!

Revision 1.11  93/08/06  08:32:11  gough
add one to param count for functions with destination pointer

Revision 1.10  93/08/05  17:43:22  gough
implement param numbers for calls and traps

Revision 1.9  93/08/05  16:49:36  gough
fix up $R's to be $T's as intended originally

Revision 1.8  93/08/05  12:13:13  gough
put in range checking on right hand side of DIV expressions.
This uses the same trap as the corresponding MOD test.

Revision 1.7  93/07/20  13:51:06  gough
the object sent to CallFunc must be determined from the function return
type, and not from the expression type (e.g. array index type ... )

Revision 1.6  93/06/30  16:25:52  mboss
remove uses of isExternal

Revision 1.5  93/06/08  08:39:49  mboss
emit EmitJumpTab _before_ CodeLabel(exitLabel) in EncodeCase.
(note that this requires a fix of an error in the dgen parser (kjg))

Revision 1.4  93/05/31  13:39:37  gough
fix for alignment of blkPars
*****************************************************************)

IMPLEMENTATION MODULE M2ObjectCode;

  IMPORT StdError;

  FROM Types    IMPORT Card16;
  FROM SYSTEM   IMPORT CAST;
  FROM Storage  IMPORT ALLOCATE, DEALLOCATE;
  FROM VARSTRS  IMPORT APPEND;
  FROM ProgArgs IMPORT Assert;

  FROM GenSequenceSupport IMPORT
        Sequence, IsEmpty, Ended, ElemPtr, InitCursor, LinkLeft,
        InitSequence, LinkRight, DisposeList, GetFirst, GetNext,
        LengthOf, NextIsLast;

  FROM M2NodeDefs IMPORT
	VarUses,
	CreateIdDesc, (* Sep-92 *)
	CreateTypeDesc, (* Oct-93 *)
        IdTree, TreeRec, FormalClass,
        IdString, IdDesc, IdRec, IdNodeClass, IdClassSet,
	StandardProcs,
        TypeDesc, TypeRec, TyNodeClass, TyClassSet,
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
(* temp for reconstructing type of designator *)
        SelectNodeClass, InitDState, EmptySelList, DesigRec,
        GetSelector, DStateType, SelectAttribute,
	AccessMode, ActualParMode;

  FROM M2RefFile IMPORT WriteRefFile;

  FROM M2DcfWrappers IMPORT WriteWrappers;

  FROM M2SSUtilities   IMPORT
	OrdinalValue, MinOfOrdType, MaxOfOrdType, IsOrdinalType, 
        IsSignedType, Compatible, IndexCardinality;

  FROM M2Alphabets     IMPORT 
	ModStateFlags, Spellix, HashBucketType, LexAttType, 
	Flags, FlagSet, ConBlock;

  FROM M2DWriter IMPORT 
	GenerateEntry, GenerateExit, LabString,
	DoObjHeader, DoObjEnd,
	Trap, Shift, LeftShift, Rotate, LineNum, CurrentLoc,
	MakeTemp, MakeWith,
	RTSproc, RTSfunc, 
	CallProc, CallFunc, CallTOSProc, CallTOSFunc, 
	MakeRetValue, GenerateReturn, FreeDescriptor, PropagateException,
	Deref, Assign, ReverseAssign, CopyBlock, CopyRecord, StrLength, 
	PushRtsAdr, PushMemTmp, (* PushDestAdr, *)
	PushCon, PushAdr, PushLit, PushTmp, 
	JumpTabDesc, JumpTabRec, CreateJumpTable, EmitJumpTable,
        PushModName, Duplicate, AllocateLabel, 
	PopNDiscard, AdjustParam, MakeFpParam, 
	MakeDstPointer, PushDstPointer,
	EmitTest, EmitAssertTest, RngAssert,
	CodeLabel, LoopLabel, LoopEnd, fallThrough,
	PushBool, CardRelop, IntRelop, 
	BigSetRelop, SetInOp, SetIncl, SetExcl, SetRelop, 
	RealRelop, SRealRelop,
	AbsInt, AbsFlt, AbsDbl,
	Branch, BranchEQZ, BranchNEZ, Switch,
	BitAND, BitOR, BitXOR, BitNegate,
	NegateBool, NegateInt, Mod, Rem, Slash,
	AddOffset, AddAdr,
	Sub, Div, Add, Mul,
	NegateFlt, NegateDbl,
	AddFlt,SubFlt,MulFlt,SlashFlt,
	AddDbl,SubDbl,MulDbl,SlashDbl,
	DFloat, FFloat, ItoF, ItoD,
	TruncD, TruncF, FtoD, DtoF,
	FloorD, FloorF, RoundD, RoundF,
        FlattenAdr, WriteByte,
	MakeIntLong, MakeCrdLong, MakeWord, NegateLong, HugeRelop,
	MulLong, AddLong, SubLong, 
	SlashLong, RemLong, DivLong, ModLong,
	AbsLong, HFloat, HTrunc, HRound, HEntier;

  FROM M2TabInitialize IMPORT PointerTo;

  FROM M2DDefinitions IMPORT Object, LabelType, ModeEnum;

  FROM M2RTSInterface IMPORT 
	InitTable, m2_casTrp, m2_funTrp, m2_assTrp, m2_preTrp,
	exitTrp, abortTrp, timeTrp, fVec,
	cap2, cap3, cup2, cup3, xor2, xor3, dif2, dif3, clr, 
        setRngIncl,
	m2_iTrpLHU, m2_iTrpLHI, m2_rTrpLHU, m2_modTrp,
	m2_rTrpLHI, m2_rTrpHU, m2_rTrpLI;

  FROM M2ProcState IMPORT GetActuals, ParInfo;

  FROM M2MachineConstants IMPORT 
	bigEndian, bitsInWord, bytesInWord, parsFixed,
	oP1,oP2,oP3,oP4,oP5, alignMap, paramMap, intMax, expandTests, 
	refRecords, sunStructs, bytesInReal;

  FROM M2NamGenerate   IMPORT callSmbl;
  FROM M2NameHandler   IMPORT EnterString, StringTable;
  FROM M2LitChain      IMPORT literalZero;

  CONST invariant = unresolved;
	localT    = directLocl;
	pointerT  = indirect;
	unknownT  = refOverwrite;

  VAR   hMinBkt, hMaxBkt, xpndBkt, 
	chCatBkt, ssCatBkt, stCatBkt : HashBucketType;

(* ============================================================ *
 *	NOTES ON THE INCOPORATION OF FLOATING POINT CODE
 * ============================================================ *
 *
 *  The D-Codes distinguish between single and double precision
 *  operations, and the meaning of operators is deduced from the
 *  actual operands in each case.
 *
 *  The only tricky case is that of literal RR's. Since this 
 *  type is compatible with both single and doubles it is 
 *  necessary to make a discrimination at code generation time.
 *  M2Traverse could do this, but at the expense of becoming
 *  non-standard. So in this case, operands are checked for 
 *  destination type and converted at compile time. 
 *  Code which does this is occurs in four contexts:
 *
 *	* within fp expressions
 *	* in fp literal assignments
 *	* in fp literal actual params
 *	* in fp relational expressions
 *
 *  New June 94 => instead of pushing literal singles, they are
 *		   deref'd from cDat. RR's are allocated 12 bytes
 *		   so (rtOffset + 8) is now the offset to single
 *
 * ============================================================ *)

(* ============================================================ *
 *	NOTES ON THE CREATION AND USE OF AGGREGATE VALUES	*
 * ============================================================ *
 *								*
 *  Expression values are created in several contexts ---	*
 *	c1. as right hand sides of assignments			*
 *	c2. as actual value parameters				*
 *	c3. as function values to be returned			*
 *								*
 *  These values may arise from the following operations ---	*
 *	o1. reference to a memory object			*
 *	o2. creation by inline expression			*
 *	o3. creation by a constructor				*
 *	o4. return by a function procedure			*
 *								*
 *  The o1 (entire object copy) case is straightforward in 	*
 *  all contexts, and never requires the allocation of a 	*
 *  memory temporary ---					*
 *   o1-c1. the assignment is performed by a blkCp		*  d := x
 *   o1-c2. (record actuals) the caller copies, using blkPar	*  f(x)
 *	(arrays, sets actuals) the caller pushes a reference  	*
 *	to the memory object itself and the callee copies	*
 *	In the case of sunStructs, a blkCp is followed by the   *
 *	passing of the address to the called procedure		*
 *   o1-c3. (return an entire object) a blkCp is performed to	*  RETURN x
 *	the destination address (previously records only!)	*
 *								*
 *  The o2 (inline expression) this case only arises for 	*
 *  set-valued expressions ---					*
 *   o2-c1. (set assignments) the value is constructed in 	*  d := a+b
 *	the dst location. No memory temps are involved unless	*
 *	these are required internally in the set expression	*
 *   o2-c2. (set actuals) M2SetTemporaries allocates a dest	*  f(a+b)
 *	location into which the expression is computed. A	*
 *	reference to this temporary is passed to the callee	*
 *   o2-c3. (return a set expression) the set is constructed 	*  RETURN a+b
 *	in the destination location (new!). This is always	*
 *	safe, since the destination is always a memory temp	*
 *								*
 *  The o3 (runtime constructor) this originally arose with set	*
 *  constructors only, but now applies to all runtime contructs *
 *   o3-c1. (set constructor assign) the value is constructed	*  d := T{...}
 *	in the dest loc. Two codegen temps are used (changed!)	*
 *	(other constructors) a memory temp is allocated, the    *
 *	value is constructed in this, and then block copied.
 *   o3-c2. (set actuals) the value is constructed in the	*  f(T{...})
 *	temporary allocated by M2SetTemporaries, a reference	*
 *	to this is passed to the callee, same for other types   *
 *	(for record constructors this might be optimized?)	*
 *   o3-c3. (return a constructor) the value is constructed	*  RETURN T{...}
 *	in the destination location, which is always an		*
 *	allocated memory temporary (new!)			*
 *								*
 *  The o4 (function value) case arises in all contexts. In all	*
 *  cases the compiler allocates a temporary for the result ---	*
 *   o4-c1. (assign a function value) a temporary is _always_	*  d := g()
 *	allocated for the result, the func is called, and a 	*
 *	blkCp emitted						*
 *   o4-c2. (func value is actual) a temporary is _always_	*  f(g())
 *	allocated for the result, and the func is called 	*
 *   o4-c3. (return a func value) the outgoing destination	*  RETURN g()
 *	is used as destination for the function call. This	*
 *	optimization is always safe since the ultimate dest	*
 *	is always an allocated memory temporary			*
 *								*
 * ============================================================ *
 *		CASTs of large objects ...			*
 *								*
 *  Casts are syntactically function calls, but do not generate *
 *  a change of stack context etc.  These appear to be cases of *
 *  o4 type to this module, but require special treatment.	*
 *   o4-c1. the pushing of the "dst address" of the rhs is	*  d := CAST(.)
 *	subverted to build the argument (if necessary) and to   *
 *	push this arg-address instead. The AssignFuncResult it  *
 *	also subverted to become a null operation, allowing the *
 *	usual blkCp to complete the assignment			*
 *   o4-c2. the pushing of the func dest address and the call   *  f(CAST(.))
 *	of AssignFuncResult are subverted as above, leaving a   *
 *	a plain blkCp						*
 *   o4-c3. the subversion of the AssignFuncResult of the other *  RETURN
 *	cases is incorrect in this case. The cast value must    *	CAST(.)
 *	actually be copied to the true destination. Thus the    *
 *	castP case is trapped, and a normal assignment is done  *
 *	with the return code for the non-function-call cases	*
 *								*
 * ============================================================ *)

(* ============================================================ *)

  CONST BranchFalse = BranchEQZ;
	BranchTrue  = BranchNEZ;

(* ============================================================ *)

  TYPE  ClassMap = ARRAY TyNodeClass OF Object;
        TempIndex = CARDINAL;
        Location = RECORD
                     name : HashBucketType;
                     index : CARDINAL;
                   END;

  CONST specials = TyClassSet{arrays,records,SS};
     (* this is the set of classes which require special assignment *)
     (* in the following table specials have the dummy entry word  *)

  CONST realClasses   = TyClassSet{RR, floats, doubles};
	scalarClasses = TyClassSet{II .. bytes, procTypes .. S1, subranges};

  CONST procSet = IdClassSet{procNode, procHeader, externProc};


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
	exceptDesc   : IdDesc;		(* exception descriptor *)
	retryLab     : LabelType; 	(* emitted in normal body if hasExcept *)
	returnLab    : LabelType;

  VAR	charPtr      : TypeDesc;
     	funcDestDesc : DesigRec;


  TYPE  ModeMap = ARRAY (* sign *)BOOLEAN, (* test *)BOOLEAN OF ModeEnum;
  CONST divMode = ModeMap{{crdV,crdV},{intV,intV}};
	addMode = ModeMap{{none,crdV},{none,intV}};

  (* ================================================== *)

  PROCEDURE BaseObjOf(ty : TypeDesc) : Object;
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
  END BaseObjOf;

  PROCEDURE BaseTypeOf(ty : TypeDesc) : TypeDesc;
  BEGIN
    IF ty^.tyClass = subranges THEN RETURN ty^.hostType;
    ELSE RETURN ty;
    END;
  END BaseTypeOf;
  (* ================================================== *)

  PROCEDURE NeedsCopy(class : TyNodeClass; size : CARDINAL) : BOOLEAN;
  BEGIN
    RETURN (class IN specials) OR ((class = sets) AND (size > bytesInWord));
  END NeedsCopy;

  (* ================================================== *)

      PROCEDURE TypeOfDes(des : DesigRec) : TypeDesc;
        VAR typ : TypeDesc;
            stt : DStateType;
            val : SelectAttribute;
      BEGIN
        IF des.variable^.idClass = varNode  THEN
          typ := des.variable^.varType;
	ELSIF (des.variable^.idClass = procHeader) OR
	      (des.variable^.idClass = externProc) OR
	      (des.variable^.idClass = procNode) THEN
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
      END TypeOfDes;

  (* ================================================== *)
  MODULE InLineTests;
    IMPORT ModeEnum,
	   invariant, unknownT, AccessModeOf,
	   EmitTest, expandTests, intMax, bytesInWord,
	   Assign, PushLit, Trap, AllocateLabel,
           MinOfOrdType, MaxOfOrdType, IsSignedType,
	   IsOrdinalType, ExprNodeClass, Object,
           IntRelop, CardRelop, BranchTrue, BranchFalse,
           PushAdr, PushTmp, oP1,oP2,oP3,oP4,oP5,
	   TempIndex, AdjustParam, AddOffset,
	   MakeTemp, Duplicate,
	   Add, Sub, IdDesc, AccessMode, Deref,
	   m2_iTrpLHU, m2_iTrpLHI, m2_rTrpLHU,  
	   m2_rTrpLHI, m2_rTrpHU,  m2_rTrpLI,
	   m2_modTrp, CAST,
	   TyNodeClass, MakeWord,
	   MakeIntLong, MakeCrdLong, HugeRelop, SubLong,
           TypeDesc, CodeLabel, LabelType;
    EXPORT IndexCheck, OpenIndexCheck, StringIndexCheck, 
	   Test, ModTest, VariableCheck;

    VAR xLab : LabelType;

    (*
     *  NOTE on duplicate and popN instructions in this module
     *
     *  In interpreted versions there is no requirement to
     *  fit in with the compile-time housekeeping of the
     *  shadow stack automaton. Thus the duplicate and pop
     *  instructions which are logically needed can be left
     *  out in the case of traps which are taken
     *  This saves some of the space used by trap calls.
     *
     *  In native code versions it would be possible to
     *  skip the Duplicate() call, and pop one less than
     *  the number of parameters after the call ...
     *)

    PROCEDURE ModTest();
      VAR exitLab : LabelType;
    BEGIN
      IF expandTests THEN
	AllocateLabel(xLab);
	Duplicate();
	PushLit(0);
	IntRelop(lessNode);
	BranchFalse(xLab);
	Trap(m2_modTrp,0);
	CodeLabel(xLab);
      ELSE
	EmitTest(m2_modTrp,1,intMax);
      END;
    END ModTest;

    PROCEDURE DblTst(low, high : CARDINAL);
    (* pre    : value to be tested is on top of stack   *)
    (* post   : value still on top, test is emitted     *)
    BEGIN
      Duplicate;
      IF low <> 0 THEN
        PushLit(low);
        Sub(none);
      END;
      PushLit(high - low);
      CardRelop(greaterNode);
      BranchFalse(xLab);
      (* now value is on tos again *)
      Duplicate;
      AdjustParam(bytesInWord,oP3); (* new DEC 91 *)
      PushLit(high);
      AdjustParam(bytesInWord,oP2); (* new DEC 91 *)
      PushLit(low);
      AdjustParam(bytesInWord,oP1); (* new DEC 91 *)
    END DblTst;

    PROCEDURE UppTst(high : CARDINAL);
    (* pre    : value to be tested is on top of stack   *)
    (* post   : value still on top, test is emitted     *)
    BEGIN
      Duplicate;
      PushLit(high);
      CardRelop(greaterNode);
      BranchFalse(xLab);
      (* now value is on tos again *)
      Duplicate;
      AdjustParam(bytesInWord,oP2); (* new DEC 91 *)
      PushLit(high);
      AdjustParam(bytesInWord,oP1); (* new DEC 91 *)
    END UppTst;

    PROCEDURE LowTst(low : INTEGER);
    (* pre    : value to be tested is on top of stack   *)
    (* post   : value still on top, test is emitted     *)
    BEGIN
      Duplicate;
      PushLit(low);
      IntRelop(lessNode);
      BranchFalse(xLab);
      (* now value is on tos again *)
      Duplicate;
      AdjustParam(bytesInWord,oP2); (* new DEC 91 *)
      PushLit(low);
      AdjustParam(bytesInWord,oP1); (* new DEC 91 *)
    END LowTst;

    PROCEDURE OpenIndexCheck(hiDes : IdDesc;
			     uplev : BOOLEAN);
    BEGIN
      AllocateLabel(xLab);
      Duplicate;
      IF uplev THEN PushAdr(hiDes,uplevel);
      ELSE PushAdr(hiDes,directLocl);
      END;
      Deref(word,hiDes,invariant);		(* high value is tos *)
      CardRelop(lessEqNode);
      BranchTrue(xLab);
      Duplicate;
      AdjustParam(bytesInWord,oP3); (* new DEC 91 *)
      IF uplev THEN PushAdr(hiDes,uplevel);
      ELSE PushAdr(hiDes,directLocl);
      END;
      Deref(word,hiDes,invariant);		(* high value is tos again *)
      AdjustParam(bytesInWord,oP2); (* new DEC 91 *)
      PushLit(0);
      AdjustParam(bytesInWord,oP1); (* new DEC 91 *)
      Trap(m2_iTrpLHU,3);
      CodeLabel(xLab);
    END OpenIndexCheck;

    PROCEDURE StringIndexCheck(dsTmp : TempIndex);	(* descriptor tmp *)
    BEGIN
      AllocateLabel(xLab);
      Duplicate;
      PushTmp(dsTmp);
      AddOffset(bytesInWord);
      Deref(word,NIL,unknownT);
      PushLit(1);		
      Add(none);
      CardRelop(lessNode);
      BranchTrue(xLab);
      Duplicate;
      AdjustParam(bytesInWord,oP3);
      PushTmp(dsTmp);
      AddOffset(bytesInWord);
      Deref(word,NIL,unknownT);
      AdjustParam(bytesInWord,oP2);
      PushLit(0);
      AdjustParam(bytesInWord,oP1);
      Trap(m2_iTrpLHI,3);
      CodeLabel(xLab);
    END StringIndexCheck;

    PROCEDURE VariableCheck(tmp : TempIndex; low : INTEGER);
      (* checks that tos is in [low .. tmpVal] *)
    BEGIN
      AllocateLabel(xLab);
      Duplicate;
      IF low <> 0 THEN		(* fix kjg Sep-92 *)
        PushLit(low);		
        Sub(none);
        PushTmp(tmp);
        PushLit(low);
        Sub(none);  (* max is on tos, test val below *)
      ELSE
        PushTmp(tmp);
      END;
      CardRelop(greaterNode);
      BranchFalse(xLab);
      (* error, trap must be emitted *)
      Duplicate;
      AdjustParam(bytesInWord,oP3); (* new DEC 91 *)
      PushTmp(tmp);
      AdjustParam(bytesInWord,oP2); (* new DEC 91 *)
      PushLit(low);
      AdjustParam(bytesInWord,oP1); (* new DEC 91 *)
      Trap(m2_rTrpLHI,3);
      CodeLabel(xLab);
    END VariableCheck;

    PROCEDURE IndexCheck(typ : TypeDesc);
      VAR min,max : INTEGER;
    BEGIN
      IF  expandTests THEN
        AllocateLabel(xLab);
        DblTst(typ^.minRange,typ^.maxRange);
        IF IsSignedType(typ) THEN
          Trap(m2_iTrpLHI,3);
        ELSE
          Trap(m2_iTrpLHU,3);
        END;
        CodeLabel(xLab);
      ELSE
	min := CAST(INTEGER,typ^.minRange);
	max := CAST(INTEGER,typ^.maxRange);
        IF IsSignedType(typ) THEN
          EmitTest(m2_iTrpLHI,min,max);
        ELSE
          EmitTest(m2_iTrpLHU,min,max);
        END;
      END;
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
        AllocateLabel(xLab);
        IF IsSignedType(srcTyp) THEN (* signed source *)
          IF NOT dSgnd AND (dMax.i < 0) THEN dMax.i := sMax.i END;
	  IF NOT expandTests THEN
	    EmitTest(m2_rTrpLHI,dMin.i,dMax.i);
	  ELSIF (sMin.i >= dMin.i) AND (sMax.i <= dMax.i) THEN
            (* skip *)
	  ELSIF sMax.i <= dMax.i THEN
	    (*
	     *  signed, single ended check of value
	     *  against the min bound of destination
	     *)
	    LowTst(dMin.i);
	    Trap(m2_rTrpLI,2);
	    CodeLabel(xLab);
          ELSE 
            (*
             *  signed and double ended checks 
             *  are done using the cardinal tests
             *  but jump to the alternate trap point
             *)
            DblTst(dMin.c,dMax.c);
            Trap(m2_rTrpLHI,3);
            CodeLabel(xLab);
          END;
        ELSE (* unsigned source *)
          IF dSgnd AND (dMin.i < 0) THEN dMin.c := 0 END;
	  IF NOT expandTests AND (dMax.c <= intMax) THEN
	    EmitTest(m2_rTrpLHU,dMin.i,dMax.i);
          ELSIF sMin.c >= dMin.c THEN
            IF sMax.c <= dMax.c THEN (* skip *)
            ELSE (* single ended check *)
              UppTst(dMax.c);
              Trap(m2_rTrpHU,2);
              CodeLabel(xLab);
            END;
          ELSE (* double ended check *)
            DblTst(dMin.c,dMax.c);
            Trap(m2_rTrpLHU,3);
            CodeLabel(xLab);
          END;
        END;
    END Test;

  END InLineTests;
  (* ================================================== *)

  TYPE  ExprClassSet = SET OF ExprNodeClass;
  CONST setBinops = ExprClassSet{starNode,slashNode,plusNode,minusNode};
        binops = ExprClassSet{andNode .. inNode};

  PROCEDURE ConstDesignator(exp : ExprDesc);
  (* post : the address of the designator is on the top of stack *)
    VAR mod : AccessMode;
  BEGIN
    mod := invariant;
    PushCon(exp^.rtOffset);
    IF NOT EmptySelList(exp^.name) THEN Selectors(exp^.name,mod) END;
  END ConstDesignator;

  PROCEDURE PushDesig(des : DesigRec; VAR idd : IdDesc; VAR mod : AccessMode);
  BEGIN
    mod := AccessModeOf(des);
    idd := des.variable;
    PushAdr(idd,mod);
    IF NOT EmptySelList(des) THEN Selectors(des,mod) END;
  END PushDesig;

  PROCEDURE Designator(des : DesigRec);
  (* post : the address of the designator is on the top of stack *)
    VAR mod : AccessMode;
  BEGIN
    mod := AccessModeOf(des);
    PushAdr(des.variable,mod);
    IF NOT EmptySelList(des) THEN Selectors(des,mod) END;
  END Designator;

  PROCEDURE DerefDesig(des : DesigRec; obj : Object);
    VAR mod : AccessMode;
  BEGIN
    mod := AccessModeOf(des);
    PushAdr(des.variable,mod);
    IF NOT EmptySelList(des) THEN Selectors(des,mod) END;
    Deref(obj,des.variable,mod);
  END DerefDesig;

  PROCEDURE AssignDesig(des : DesigRec; obj : Object);
    VAR mod : AccessMode;
  BEGIN
    mod := AccessModeOf(des);
    PushAdr(des.variable,mod);
    IF NOT EmptySelList(des) THEN Selectors(des,mod) END;
    Assign(obj,des.variable,mod);
  END AssignDesig;

  PROCEDURE PushOpenElemSize(high : IdDesc; elTyp : TypeDesc; uplev : BOOLEAN);

    PROCEDURE RealElType(first : IdDesc; elTyp : TypeDesc) : TypeDesc;  
    BEGIN
      WHILE first <> NIL DO	(* find real element type ... *)
        elTyp := elTyp^.elementType;
        first := first^.nextHigh;
      END;
      RETURN elTyp;
    END RealElType;

  BEGIN
    high  := high^.nextHigh;
    elTyp := RealElType(high,elTyp);
    PushLit(elTyp^.size);
    WHILE high <> NIL DO
      IF uplev THEN
	PushAdr(high,uplevel);
      ELSE
	PushAdr(high,highAccess);
      END;
      Deref(word,high,invariant);		(* high value is tos *)
      PushLit(1);
      Add(none);
      Mul(none);
      high  := high^.nextHigh;
    END;
  END PushOpenElemSize;

 (*	 						 (* jl Jun 94 *)
  * This function reflects the changes to FixLiteral()
  * 0.0 is marked and not put on the literal chain
  * otherwise floats are stuck in after the double literal
  *)
  PROCEDURE PushFloatConst(exp : ExprDesc);
  BEGIN
    IF exp^.rtOffset = literalZero THEN
      PushLit(0); ItoF;
    ELSE
      PushCon(exp^.rtOffset + bytesInReal);
      Deref(float,NIL,invariant);
    END;
  END PushFloatConst;

  PROCEDURE ConstPart(exp : ExprDesc) : CARDINAL;
  BEGIN
(* $T- *)      (* these incs and decs could be by signed amounts ... *)
    WITH exp^ DO 
      IF exprClass = literalNode THEN
	RETURN OrdinalValue(exprType,conValue);
      ELSIF exprClass = plusNode THEN
	RETURN ConstPart(leftOp) + ConstPart(rightOp);
      ELSIF exprClass = minusNode THEN
	RETURN ConstPart(leftOp) - ConstPart(rightOp);
      ELSIF (exprClass = starNode) THEN
	IF (rightOp^.exprClass = literalNode) THEN 
	  RETURN ConstPart(leftOp) * 
			OrdinalValue(rightOp^.exprType,rightOp^.conValue);
        ELSIF (leftOp^.exprClass = literalNode) THEN 
	  RETURN ConstPart(rightOp) * 
			OrdinalValue(leftOp^.exprType,leftOp^.conValue);
        ELSE RETURN 0;
        END;
      ELSE RETURN 0;
      END;
    END;
(* $T= *)
  END ConstPart;

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
	ELSIF hasROp THEN NegateInt(FALSE);
	END;
      ELSIF (exprClass = starNode) AND
	    ((rightOp^.exprClass = literalNode) OR
	     (leftOp^.exprClass = literalNode)) THEN
	IF rightOp^.exprClass = literalNode THEN
	  PushVariablePart(leftOp);
	  PushLit(OrdinalValue(rightOp^.exprType,rightOp^.conValue));
	ELSE (* leftOp is literal *)
	  PushVariablePart(rightOp);
	  PushLit(OrdinalValue(leftOp^.exprType,leftOp^.conValue));
	END;
	Mul(none);
      ELSE PushExprValue(exp);
      END;
    END;
(* $T= *)
  END PushVariablePart;

  PROCEDURE Selectors(des : DesigRec; VAR mod : AccessMode);
    VAR dState : DStateType;
	currTp : TypeDesc;
	indTp  : TypeDesc;
	highD  : IdDesc;
        attrib : SelectAttribute;
	offsetTotal : INTEGER;
	constIndex, lVal : CARDINAL;
	elSize  : CARDINAL;
	sizeOpn : BOOLEAN;
	isUplev : BOOLEAN;
	idxTemp : TempIndex;

    PROCEDURE ScaleAndAdd(siz : CARDINAL);
    BEGIN
      IF siz = 0 THEN
        PushOpenElemSize(highD,currTp,isUplev);
        Mul(none);
      ELSIF siz > 1 THEN
        PushLit(siz);
        Mul(none);
      END;
      AddAdr();
    END ScaleAndAdd;

  BEGIN
    offsetTotal := 0;
    InitDState(des,dState);
    highD  := des.variable;
    currTp := des.variable^.varType;
    isUplev := (AccessModeOf(des) >= uplevel);
(* $T-  all offsets are calculated modulo 2**32 *)
    LOOP
     (*
      *  If the current type is an opaque temp we
      *  must resolve it to the real pointer type.
      *  (How did this one escape until 1996? kjg)
      *)
      IF currTp^.tyClass = opaqueTemp THEN
        currTp := currTp^.resolvedType;
      END;
      GetSelector(dState,attrib);
      CASE attrib.tag OF
        | fieldExtractNode :
            INC(offsetTotal,attrib.fid^.fieldOffset);
            currTp := attrib.fid^.fieldType;
        | subscriptNode :
            IF currTp^.tyClass = stringTs THEN
	      IF offsetTotal <> 0 THEN		(* -|,ptr	*)
	        AddOffset(offsetTotal);
	        offsetTotal := 0;
	      END;
	      idxTemp := attrib.exp^.sourceLoc.pos;
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
              Deref(word,des.variable,mod);	(* -|,blk	*)
	      MakeTemp(idxTemp);
              Deref(word,NIL,pointerT);		(* -|,mem	*)
              mod     := pointerT;
              currTp  := currTp^.targetType;
              PushExprValue(attrib.exp);
              IF indexTests IN attrib.exp^.testFlags THEN
	        StringIndexCheck(idxTemp);
              END;
              ScaleAndAdd(currTp^.size);	(* -|,mem+ofst	*)
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
                      OpenIndexCheck(highD,isUplev);
                    ELSIF exprType^.minRange > MAX(INTEGER) THEN
                      EmitTest(m2_iTrpLHI,0,MAX(INTEGER));
                    END;
                  END;
                  ScaleAndAdd(elSize);
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
                    INC(offsetTotal,ConstPart(attrib.exp) * elSize);
(* $T= *)         END;
                  ScaleAndAdd(elSize);
                END;
              END; (* with *)
            END;
	| dereferenceNode :
	    IF offsetTotal <> 0 THEN
	      AddOffset(offsetTotal);
	      offsetTotal := 0;
	    END;
	    Deref(word,des.variable,mod); 
	   (*
	    *  From here until the end of the
	    *  selector list the mode is pointerT
	    *)
	    mod := pointerT;
	    currTp := currTp^.targetType;
	| endMarker : 
	    IF offsetTotal <> 0 THEN
	      AddOffset(offsetTotal);
	    END;
	    EXIT;
      END;
    END;
  END Selectors;

  PROCEDURE PushOpenCount(desig : ExprDesc);
    VAR uplev : BOOLEAN;
        highD : IdDesc;
  BEGIN
    uplev := (AccessModeOf(desig^.name) >= uplevel);
    highD := desig^.name.variable^.nextHigh;
    IF uplev THEN
      PushAdr(highD,uplevel);
    ELSE
      PushAdr(highD,highAccess);
    END;
    Deref(word,highD,invariant);		(* high value is tos *)
    PushLit(1);
    Add(none);
    highD := highD^.nextHigh;
    WHILE highD <> NIL DO
      IF uplev THEN
        PushAdr(highD,uplevel);
      ELSE
        PushAdr(highD,highAccess);
      END;
      Deref(word,highD,invariant);		(* high value is tos *)
      PushLit(1);
      Add(none);
      Mul(none);
      highD := highD^.nextHigh;
    END;
  END PushOpenCount;

  PROCEDURE PushExprAddress(exp : ExprDesc);
  BEGIN
    WITH exp^ DO
      CASE exprClass OF
      | desigNode : Designator(name);
      | selConstNode : ConstDesignator(exp);
      | literalNode : PushCon(rtOffset);
      | castNode : 
	 (*
	  *  structure:
	  *	source  : ExprDesc  -- points to source expression
	  *	needTmp : BOOLEAN   -- does this case need a temp
	  *	wrd2wrd : BOOLEAN   -- a possibly shortening cast
	  *	tempId  : IdDesc    -- name of temporary variable
	  *     exprType : TypeDesc -- destination type descriptor
	  *)
          IF needTmp THEN
	    PushAdr(tempId,directLocl);
	    Duplicate;
	    IF NeedsCopy(source^.exprType^.tyClass,source^.exprType^.size) THEN
(*
 *	      StdError.WriteString("11 BlkCp, into and out of temp" + 12C);
 *)
              MakeObjAndPushAdr(source);
	      IF source^.exprType^.tyClass <> SS THEN
                PushLit(source^.exprType^.size);	(* source size *)
	      ELSIF source^.conValue.strHigh >= exprType^.size THEN
                PushLit(exprType^.size);		(* dest size   *)
	      ELSE
                PushLit(source^.conValue.strHigh + 1);    (* string size *)
	      END;
	      CopyBlock(source^.exprType^.alignMask);
	    ELSE
	      PushExprValue(source);
	      ReverseAssign(BaseObjOf(source^.exprType),tempId,directLocl);
(*
 *	      StdError.WriteString("12 Assign in, BlkCp out of temp" + 12C);
 *)
	    END;
	  ELSE
(*
 *	    StdError.WriteString("13 Blkcp directly, don't need temp" + 12C);
 *)
	    MakeObjAndPushAdr(source);
	  END;
      | preconNode :
	  StatementSeq(exp^.evalLst,0);
	  PushExprAddress(exp^.theCall);
      | funcDesigNode : 
	  PushMemTmp(exp^.sourceLoc.pos);
      | setDesigNode, constructorNode : 
	  PushMemTmp(setConDest);
      ELSE  PushMemTmp(setOpDest); 
      END;
    END;
  END PushExprAddress;

  PROCEDURE MakeObjAndPushAdr(elem : ExprDesc);
   (* post : object is built, and address is pushed *)
  BEGIN
      PushExprAddress(elem);
      IF (elem^.exprType^.tyClass = sets) AND
	  (elem^.exprType^.size > bytesInWord) THEN	(* fix kjg 4-Mar-93 *)
        BuildBigSet(elem,elem^.exprType^.size DIV bytesInWord);
      ELSIF elem^.exprClass = funcDesigNode THEN
        (* relies on dst address being top of stack, but... *)
        AssignFuncResult(elem,FALSE);		(* no pop *)
      ELSIF elem^.exprClass = constructorNode THEN
        (* relies on dst address being top of stack, but... *)
        ConstructSeq(elem);			(* no pop *)
      END;
  END MakeObjAndPushAdr;

  PROCEDURE ConstructSeq(elem : ExprDesc);
  (* pre  : dest address in on the top of stack *)
  (* post : top of stack is unchanged by call   *)
    VAR tClass : TyNodeClass;
	eClass : ExprNodeClass;
	exTyp  : TypeDesc;
	eCurs  : ElemPtr;
	range  : RangeDesc;
	object : Object;
	needCp : BOOLEAN;
	count  : CARDINAL;
	repOff : INTEGER;
	uTmp   : TempIndex;
  BEGIN
    InitCursor(elem^.rangeSeq,eCurs);
    uTmp := elem^.sourceLoc.pos;
    MakeTemp(uTmp);
    WHILE NOT Ended(eCurs) DO
      GetNext(eCurs,range);
      WITH range^ DO
        exTyp  := lower^.exprType;
        tClass := exTyp^.tyClass;
        eClass := lower^.exprClass;
	needCp := NeedsCopy(tClass, exTyp^.size);
        IF NOT needCp THEN
          PushExprValue(lower);
          IF rangeTests IN lower^.testFlags THEN 
  	    Test(desigType,exTyp); (* dst,src *)
          END;
	  PushTmp(uTmp); AddOffset(elemOffset);
          object := BaseObjOf(desigType);
          Assign(object,NIL,directLocl);	(* pops the dst adrs *)
	ELSIF eClass = funcDesigNode THEN	(* create res in dst *)
	  PushTmp(uTmp); AddOffset(elemOffset);
          AssignFuncResult(lower,TRUE);		(* pops the dst adrs *)
	ELSIF eClass = constructorNode THEN	(* construct in dest *)
	  PushTmp(uTmp); AddOffset(elemOffset);
	  ConstructSeq(lower); PopNDiscard;	(* pops the dst adrs *)
	ELSE					(* build, then copy  *)
	  PushTmp(uTmp); AddOffset(elemOffset);
          MakeObjAndPushAdr(lower);
          PushLit(desigType^.size);
          CopyBlock(exTyp^.alignMask);		(* pops the dst adrs *)
        END;
	IF upper <> NIL THEN
	  repOff := elemOffset;
	  FOR count := 1 TO upper^.count - 1 DO
	    INC(repOff,desigType^.size);
	    IF needCp THEN
	      PushTmp(uTmp); AddOffset(repOff);	      	      (* dst *)
	      PushTmp(uTmp); AddOffset(elemOffset);	      (* src *)
              PushLit(desigType^.size);
              CopyBlock(exTyp^.alignMask);
            ELSE 
	      PushTmp(uTmp); AddOffset(elemOffset);	      (* src *)
	      Deref(object,NIL,directLocl);
	      PushTmp(uTmp); AddOffset(repOff);	     	      (* dst *)
              Assign(object,NIL,directLocl);
            END; (* if *)
	  END; (* for *)
	END; (* if upper<>NIL *)
      END; (* with *)
    END; (* while *)
  END ConstructSeq;

  PROCEDURE BoolJump(exp : ExprDesc;
		     fLab, tLab : LabelType);
    VAR class : TyNodeClass;
	local : LabelType;
	size  : CARDINAL;
  BEGIN
    CASE exp^.exprClass OF
    | preconNode :
	StatementSeq(exp^.evalLst,0);
	BoolJump(exp^.theCall,fLab,tLab);
    | funcDesigNode :
	PushFunctionValue(exp,exp^.paramSeq);
	IF fLab = fallThrough THEN BranchTrue(tLab);
	ELSIF tLab = fallThrough THEN BranchFalse(fLab);
	ELSE BranchFalse(fLab); Branch(tLab);
	END;
    | desigNode : 
	DerefDesig(exp^.name,byteCard);
	IF fLab = fallThrough THEN BranchTrue(tLab);
	ELSIF tLab = fallThrough THEN BranchFalse(fLab);
	ELSE BranchFalse(fLab); Branch(tLab);
	END;
    | orNode :
	local := tLab;
	IF tLab = fallThrough THEN AllocateLabel(local) END;
	BoolJump(exp^.leftOp,fallThrough,local);
	BoolJump(exp^.rightOp,fLab,tLab);
	IF tLab = fallThrough THEN CodeLabel(local) END;
    | andNode :
	local := fLab;
	IF fLab = fallThrough THEN AllocateLabel(local) END;
	BoolJump(exp^.leftOp,local,fallThrough);
	BoolJump(exp^.rightOp,fLab,tLab);
	IF fLab = fallThrough THEN CodeLabel(local) END;
    | notNode : BoolJump(exp^.notOp,tLab,fLab);
    | inNode, equalsNode .. lessEqNode, selConstNode :
	PushExprValue(exp);
	IF fLab = fallThrough THEN BranchTrue(tLab);
	ELSIF tLab = fallThrough THEN BranchFalse(fLab);
	ELSE BranchFalse(fLab); Branch(tLab);
	END;
    | literalNode : 
	IF exp^.conValue.fixValue = 0 THEN Branch(fLab);
	ELSE Branch(tLab);
	END;
    END; (* case *)
  END BoolJump;

  PROCEDURE WordSetConstructor(expr : ExprDesc);
    VAR baseTy : TypeDesc;
	uTmp   : TempIndex;

    PROCEDURE PushAnElement(range : RangeDesc);
    BEGIN
      WITH range^ DO
        IF upper = NIL THEN (* single element *)
	  PushLit(1);
	  PushExprValue(lower);
	  IF rangeTests IN lower^.testFlags THEN
	    Test(baseTy,lower^.exprType); (* dst,src *)
	  END;
	  LeftShift;
	ELSE (* a range *)
	  PushRtsAdr(fVec);
          Deref(word,NIL,invariant);          
	  PushExprValue(upper);
	  IF rangeTests IN lower^.testFlags THEN
	    MakeTemp(uTmp);
	  END;
	  IF rangeTests IN upper^.testFlags THEN
	    Test(baseTy,upper^.exprType); (* dst,src *)
	  END;
	  PushLit(bytesInWord); Mul(none);	(* jl Jun 94 *)
	  AddAdr();
	  Deref(word,NIL,invariant);
          PushLit(1);
          PushExprValue(lower);
	  IF rangeTests IN lower^.testFlags THEN
	    VariableCheck(uTmp,baseTy^.minRange);
	  END;
	  LeftShift;
	  NegateInt(FALSE);
	  BitAND;
	END; (* else a range *)
      END;
    END PushAnElement;

    VAR rngCrs : ElemPtr;
        thsRng : RangeDesc;
  BEGIN
    Assert(NOT IsEmpty(expr^.rangeSeq));
    baseTy := expr^.exprType^.baseType;
    uTmp := expr^.sourceLoc.pos;
    GetFirst(expr^.rangeSeq,rngCrs,thsRng);
    PushAnElement(thsRng);
    WHILE NOT Ended(rngCrs) DO
      GetNext(rngCrs,thsRng);
      PushAnElement(thsRng);
      BitOR;
    END;
  END WordSetConstructor;

  PROCEDURE BigSetIncl(incl : BOOLEAN; 
			tix : TempIndex;
			var : IdDesc;
			mod : AccessMode);
    (* value to be included is on top of stack *)
    (* address of set is below that on stack   *)
    (* stack is popped by two post- 	       *)
  BEGIN
    MakeTemp(tix);
    PushLit(bitsInWord);  Div(intV);	(* jl Jun 94 *)
    PushLit(bytesInWord); Mul(none);
    AddAdr(); (* address of element is on top *)
    Duplicate;
    Deref(word,var,mod);
    PushTmp(tix);
    PushLit(bitsInWord - 1); BitAND;
    IF incl THEN SetIncl;
    ELSE SetExcl;
    END;
    ReverseAssign(word,var,mod);
  END BigSetIncl;

  PROCEDURE BigSetConstructor(expr : ExprDesc;
			      size : CARDINAL;
			      pop  : BOOLEAN);
  (* pre  : destination address is on top of stack *)
  (* post : set is constructed, optional pop by 1  *)
    VAR rngCrs : ElemPtr;
        thsRng : RangeDesc;
        baseTy : TypeDesc;
	uTmp   : TempIndex;
  BEGIN
    Assert(NOT IsEmpty(expr^.rangeSeq));
    baseTy := expr^.exprType^.baseType;
    uTmp   := expr^.sourceLoc.pos; (* 2 words allocated by SetExpr *)
    MakeTemp(uTmp + bytesInWord);	(* dest adr   *)
    IF pop THEN PopNDiscard() END;
    InitCursor(expr^.rangeSeq,rngCrs);
    PushLit(size); (* ==> size in words *)
    AdjustParam(bytesInWord,oP2);	(* new DEC 91 *)
    (* next does work with interpreters    *)
    PushTmp(uTmp + bytesInWord);	(* dest adr   *)
    AdjustParam(bytesInWord,oP1);	(* new DEC 91 *)
    RTSproc(clr,2); 		
    WHILE NOT Ended(rngCrs) DO
      GetNext(rngCrs,thsRng);
      WITH thsRng^ DO
        IF upper = NIL THEN (* single element *)
	  PushTmp(uTmp + bytesInWord);	(* dest adr   *)
	  PushExprValue(lower);
	  IF rangeTests IN lower^.testFlags THEN
	    Test(baseTy,lower^.exprType); (* dst,src *)
	  END;
	  (* stack is top (val, dst, ...) *)
	  BigSetIncl(TRUE,uTmp,NIL,localT);
	ELSE (* a range *)
          (* the upper bound is checked *)
	  PushExprValue(upper);
	  IF rangeTests IN upper^.testFlags THEN
	    Test(baseTy,upper^.exprType); (* dst,src *)
	  END;
	 (* ----------------- *)
	  MakeTemp(uTmp);
	  PopNDiscard();
	 (* ----------------- *)
	  PushExprValue(lower);
	  IF rangeTests IN lower^.testFlags THEN
            (* the lower bound is checked against upper *)
	    VariableCheck(uTmp,baseTy^.minRange);
	  END;
	  PushTmp(uTmp);
          AdjustParam(bytesInWord,oP3);
          AdjustParam(bytesInWord,oP2);
	  (* order of params (dest, lower, upper ...) *)
	  PushTmp(uTmp + bytesInWord);	(* dest adr   *)
          AdjustParam(bytesInWord,oP1);	(* new DEC 91 *)
	  RTSproc(setRngIncl,3); 
        END;
      END; (* with *)
    END; (* while *)
  END BigSetConstructor;

  PROCEDURE BuildBigSet(exp : ExprDesc;
			siz : CARDINAL);
    VAR class : ExprNodeClass;
    (* post : the set is formed *)
  BEGIN
    class := exp^.exprClass;
    IF class IN setBinops THEN
      (*
       *  now, do we need an op2 or an op3?
       *  since the destination is known to be a temp
       *  we need an op2 if ---
       *     leftOp shares the destination temp, or
       *     rightOp shares the temp and op is commutative
       *  else we need an op3
       *
       *  As of September 1992 this does not leave the
       *  address on the top of the stack, and does not
       *  overlap the parameter evaluations (kjg)
       *  Also, the 3-address forms are always used
       *)
      BuildBigSet(exp^.leftOp,siz);	(* must do left first *)
      BuildBigSet(exp^.rightOp,siz);	(* must do right next *)
      PushLit(siz);
      AdjustParam(bytesInWord,oP4);	(* new DEC 91 *)
      PushExprAddress(exp^.rightOp);
      AdjustParam(bytesInWord,oP3);	(* new DEC 91 *)
      PushExprAddress(exp^.leftOp);
      AdjustParam(bytesInWord,oP2);	(* new DEC 91 *)
      PushExprAddress(exp); 
      AdjustParam(bytesInWord,oP1);	(* new DEC 91 *)
      CASE class OF
	| plusNode  : RTSproc(cup3,4); 
	| minusNode : RTSproc(dif3,4); 
	| starNode  : RTSproc(cap3,4); 
	| slashNode : RTSproc(xor3,4); 
      END;
    ELSIF class = setDesigNode THEN
      PushExprAddress(exp);
      BigSetConstructor(exp,siz,TRUE);
    ELSIF class = funcDesigNode THEN
      PushExprAddress(exp);
      AssignFuncResult(exp,TRUE);  (* call func as proc *)
    ELSIF class = preconNode THEN
      StatementSeq(exp^.evalLst,0);
      BuildBigSet(exp^.theCall,siz);
    (* ELSE literal or something *)
    END;
  END BuildBigSet;

  (*
   *   The parameter passing strategy is as follows:
   *   all the parameters are pushed onto the stack of
   *   the abstract machine in reverse order.
   *   Then the designator address is pushed, then
   *   the "call" pops the designator address
   *
   *   For native code versions, a higher level of 
   *   abstraction is required, with an arbitrary order
   *   of evaluation, and a separate MakeParam operation
   *)

  PROCEDURE DoParams(pType   : TypeDesc;
		     seq     : Sequence;
		VAR parBytes : INTEGER);

    VAR pCurs   : ElemPtr;
	minPA   : CARDINAL;
	outSeq1 : Sequence;
	outSeq2 : Sequence;
	nextPar : ParInfo;

    PROCEDURE EvalNextParam(elem : ParInfo);
      VAR class : TyNodeClass;
	  size  : CARDINAL;
	  parEx : ExprDesc;
	  pushAddr, specCase, bigSet : BOOLEAN;
    BEGIN
      WITH elem^ DO
	IF expr^.exprClass = errNode THEN RETURN END;
	class := expr^.exprType^.tyClass;
	size  := expr^.exprType^.size;
	bigSet := (class = sets) AND (size > bytesInWord);
        (*
	 *  this predicate indicates that either an
	 *  address is passed to the procedure, or
	 *  that a caller copy operation follows
	 *)
	pushAddr := (class IN specials) OR 		(* arrays,records *)
		    (expr^.actualClass >= open1D) OR
		    (expr^.actualClass = refActual) OR bigSet;

	specCase := (expr^.actualClass > open1D) AND 
		    (expr^.exprClass = fixedMarshallNode) AND
		    (expr^.actualX^.exprType^.tyClass IN scalarClasses);

  	(* now push the actual *)
	IF specCase THEN
	  PushMemTmp(expr^.sourceLoc.pos);
	  Duplicate; 
  	  PushExprValue(expr^.actualX);
        ELSIF pushAddr THEN
	  parEx := expr;
	  IF sunStructs AND
	     (class = records) AND 
	     (expr^.actualClass = valActual) THEN
	    PushMemTmp(expr^.sourceLoc.pos);
	  ELSIF expr^.exprClass = openMarshallNode THEN
	    DerefDesig(expr^.mrshPtr^.name,word);      (* push the pointer *)
	    Duplicate; 
	    parEx := expr^.actualX;
	  ELSIF expr^.exprClass = fixedMarshallNode THEN
(*
 *	    StdError.WriteString("Marshalling temp at ");
 *	    StdError.WriteCard(expr^.sourceLoc.pos,0);
 *	    StdError.WriteLn;
 *)
	    PushMemTmp(expr^.sourceLoc.pos);
	    Duplicate; 
	    parEx := expr^.actualX;
	  END;
          MakeObjAndPushAdr(parEx);
	  IF (class = stringTs) AND
	     (parEx^.actualClass >= open1D) THEN 
	    Deref(word,NIL,unknownT);
	    Duplicate;
	    Deref(word,NIL,unknownT);
	  END;
  	ELSE (* unstructured, floating point, wordset value pars *)
	  (* must check for compile-time shorten *)
	  IF (class = RR) AND (dTyp^.tyClass = floats) THEN (* shorten *)
	    PushFloatConst(expr);			  (* jl Jun 94 *)
	  ELSIF dTyp^.tyClass = hInts THEN 
	    PushLongValue(expr);
	  ELSE
  	    PushExprValue(expr);
  	    IF rangeTests IN expr^.testFlags THEN 
  	      Test(dTyp,expr^.exprType); (* dst,src *)
	    END;
  	  END;
  	END;
      END; (* with *)
    END EvalNextParam;

    PROCEDURE MakeNextParam(elem : ParInfo);

      PROCEDURE PushOpenSize(desig : ExprDesc; elTyp : TypeDesc);
      BEGIN
	PushOpenCount(desig);
	IF elTyp^.size > 1 THEN
	  PushLit(elTyp^.size);
	  Mul(none);
	END;
      END PushOpenSize;

      PROCEDURE CopyElemByElem(expr : ExprDesc);
       (*
        *   The same variables could be used by all copies, as
        *   the marshalling cannot be overlapped in calls.
        *)
	VAR lLab   : LabelType;
	    sElTyp : TypeDesc;		(* source element type   *)
	    dElTyp : TypeDesc;		(* destination elem type *)
      BEGIN
	dElTyp := expr^.exprType;	(* ultimate element type *)
	sElTyp := expr^.actualX^.exprType^.elementType;
        WHILE sElTyp^.tyClass = arrays DO
	  sElTyp := sElTyp^.elementType;
	END;
       (*
	*   Stack is ---	srcAdr <--- tos
	*			tmpAdr
	*			tmpAdr
	*
	*   First we load up three pointers with loop variables
	*)
	PushAdr(expr^.elemByElem^.src,directLocl);
	Assign(word,expr^.elemByElem^.src,directLocl);
	PushAdr(expr^.elemByElem^.dst,directLocl);
	Assign(word,expr^.elemByElem^.dst,directLocl);
	PushAdr(expr^.elemByElem^.dst,directLocl);
	Deref(word,expr^.elemByElem^.dst,directLocl);
	IF expr^.exprClass = openMarshallNode THEN
	  PushOpenSize(expr^.actualX,dElTyp);
	ELSE
	  PushLit(expr^.mrshSiz);
	END;
	AddAdr;
	PushAdr(expr^.elemByElem^.lim,directLocl);
	Assign(word,expr^.elemByElem^.lim,directLocl);
	AllocateLabel(lLab);
       (*
	*  now the loop 
	*)
	WITH expr^.elemByElem^ DO
	  LoopLabel(lLab);			(* LOOPLABEL lLab:	*)
	  PushAdr(src,directLocl);		(*	pshFP  srcOff	*)
	  Deref(word,src,directLocl);		(*	derefW		*)
	  Deref(BaseObjOf(sElTyp),NIL,unknownT);(*	derefSS		*)
  	  IF rangeTests IN expr^.actualX^.testFlags THEN 
  	    Test(dElTyp,sElTyp); (* dst,src *)
	  END;
	  PushAdr(dst,directLocl);		(*	pshFP  dstOff	*)
	  Deref(word,dst,directLocl);		(*	derefW		*)
	  Assign(BaseObjOf(dElTyp),dst,directLocl); (*	assignDS	*)
         (*
	  *  now the housekeeping 
	  *)
	  PushAdr(dst,directLocl);		(*	pshFP  dstOff	*)
	  Deref(word,dst,directLocl);		(*	derefW		*)
	  PushLit(dElTyp^.size);		(*	pshLit dstSiz	*)
	  AddAdr;				(*	addAdr		*)
	  PushAdr(dst,directLocl);		(*	pshFP  dstOff	*)
	  Assign(word,dst,directLocl);		(*	assignW		*)
	  PushAdr(src,directLocl);		(*	pshFP  srcOff	*)
	  Deref(word,src,directLocl);		(*	derefW		*)
	  PushLit(sElTyp^.size);		(*	pshLit srcSiz	*)
	  AddAdr;				(*	addAdr		*)
	  PushAdr(src,directLocl);		(*	pshFP  srcOff	*)
	  Assign(word,src,directLocl);		(*	assignW		*)
         (*
	  *  now the loop test 
	  *)
	  PushAdr(dst,directLocl);		(*	pshFP  dstOff	*)
	  Deref(word,dst,directLocl);		(*	derefW		*)
	  PushAdr(lim,directLocl);		(*	pshFP  limOff	*)
	  Deref(word,lim,directLocl);		(*	derefW		*)
	 (*
	  *   Stack is ---	limPtr <--- tos
	  *			dstPtr
	  *			tmpAdr
	  *)
	  CardRelop(lessNode);			(*	crdGE		*)
	  BranchTrue(lLab);			(*	brFalse lLab	*)
	  LoopEnd(lLab);
	END;
       (*
	*   Stack is ---	tmpAdr <--- tos
	*)
      END CopyElemByElem;

      VAR align : CARDINAL;
	  aMask : CHAR;
	  class : TyNodeClass;
	  size  : CARDINAL;
	  actualTy : TypeDesc;
	  floatPar : BOOLEAN;
	  pushAddr, bigSet : BOOLEAN;
    BEGIN
      WITH elem^ DO
	IF expr^.exprClass = errNode THEN RETURN END;
	class := expr^.exprType^.tyClass;
	size := expr^.exprType^.size;
	bigSet := (class = sets) AND (size > bytesInWord);
        (*
	 *  this predicate indicates that either an
	 *  address is passed to the procedure, or
	 *  that a caller copy operation follows
	 *)
	pushAddr := (class IN specials) OR 
		    (expr^.actualClass >= open1D) OR
		    (expr^.actualClass = refActual) OR bigSet;
	floatPar := (expr^.actualClass = valActual) AND 
			(class IN realClasses);
	(*
	 *  expression or address pushed, now we must add 
	 *  parOffset and complete copy of value record types
	 *)
	IF (class = records) AND 
	   (expr^.actualClass = valActual) 	THEN
          aMask := expr^.exprType^.alignMask;
	  IF sunStructs THEN
            PushLit(dTyp^.size);
	    CopyBlock(aMask);
	    PushMemTmp(expr^.sourceLoc.pos);
	    AdjustParam(bytesInWord,ofst);
	  ELSIF refRecords THEN
	    AdjustParam(bytesInWord,ofst);
	  ELSE
            CopyRecord(dTyp^.size,ofst,aMask);
	  END;
	ELSE (* is already on stack *)
	  IF floatPar THEN
	    MakeFpParam(dTyp^.size,ofst);
	  ELSIF (expr^.exprClass = openMarshallNode) OR
		(expr^.exprClass = fixedMarshallNode) THEN
	    actualTy := expr^.actualX^.exprType;
	   (*
	    *   Stack is ---	srcAdr <--- tos
	    *			tmpAdr
	    *			tmpAdr
	    *
	    *   unless this is a scalar being marshalled to
	    *   an universally conformant open array formal.
	    *   In that case we have ---
	    *
	    *   Stack is ---	value <--- tos
	    *			tmpAdr
	    *			tmpAdr
	    *) 
	    IF expr^.elemByElem <> NIL THEN 
	      CopyElemByElem(expr);
	    ELSIF actualTy^.tyClass = SS THEN
	      PushLit(expr^.actualX^.conValue.strHigh + 1);
	      CopyBlock(0C);
	    ELSIF expr^.exprClass = openMarshallNode THEN
              WHILE (actualTy^.tyClass = arrays) AND actualTy^.isDynamic DO
	        actualTy := actualTy^.elementType;
	      END;
	      PushOpenSize(expr^.actualX, actualTy);
	      CopyBlock(actualTy^.alignMask)
	    ELSIF actualTy^.tyClass IN scalarClasses THEN
	      ReverseAssign(BaseObjOf(actualTy),NIL,localT);
	    ELSE (* assert: no size change, so use exprType^.size *)
	      PushLit(actualTy^.size);
	      CopyBlock(actualTy^.alignMask)
	    END;
	   (*
	    *   Stack is ---	tmpAdr <--- tos
	    *)
	    AdjustParam(bytesInWord,ofst); (* pops abstract to concrete stack *)
          ELSIF pushAddr OR (dTyp^.size = bytesInWord) THEN 
	    AdjustParam(bytesInWord,ofst); (* pops abstract to concrete stack *)
(* #### *)
	    IF (class = stringTs) AND
	       (expr^.actualClass >= open1D) THEN (* calculate high here ... *)
	      AddOffset(bytesInWord);
	      Deref(word,NIL,unknownT);
	      IF indexTests IN expr^.testFlags THEN 
			Test(PointerTo(cards),PointerTo(ints)) END;
	      IF expr^.actualClass >= byteOpen THEN
		IF expr^.actualClass = byteOpen THEN
		  size := expr^.exprType^.targetType^.size;
		ELSE (* expr^.actualClass = wordOpen *)
		  size := expr^.exprType^.targetType^.size DIV bytesInWord;
		END;
		IF size <> 1 THEN
		  PushLit(1); Add(none); PushLit(size);
		  Mul(none); PushLit(1); Sub(none);
		END;
	      END;
	      AdjustParam(bytesInWord,ofst+(oP2-oP1)); (* stackUpwrite kludge *)
	    END;
(* #### *)
	  ELSIF dTyp^.size = 8 THEN
	    AdjustParam(8,ofst);	   (* pops abstract to concrete stack *)
	  ELSE 
            AdjustParam(minPA,ofst);
          END;
	END; (* if class = records *)
      END; (* with *)
    END MakeNextParam;

    PROCEDURE ReverseEval(curs : ElemPtr);
      VAR next : ParInfo;
    BEGIN
      IF Ended(curs) THEN RETURN;
      ELSE
        GetNext(curs,next);
        ReverseEval(curs);  (* recursively do rest of list first *)
        EvalNextParam(next);
      END;
    END ReverseEval;

  BEGIN (* DoParams *)
    minPA := ORD(paramMap[0C]) + 1;
    GetActuals(seq,pType,parBytes,outSeq1,outSeq2);
    InitCursor(outSeq1,pCurs);
    ReverseEval(pCurs);
    InitCursor(outSeq1,pCurs);
    WHILE NOT Ended(pCurs) DO
      GetNext(pCurs,nextPar);
      MakeNextParam(nextPar);
    END;
    InitCursor(outSeq2,pCurs);
    WHILE NOT Ended(pCurs) DO
      GetNext(pCurs,nextPar);
      EvalNextParam(nextPar);
      MakeNextParam(nextPar);
    END;
  END DoParams;

  PROCEDURE PushFunctionValue(exp : ExprDesc;
			      seq : Sequence);

      VAR parBytes : INTEGER;
	  pNum     : CARDINAL;
          des      : DesigRec;

      PROCEDURE CallStandardFunc(id : StandardProcs);
	VAR curs  : ElemPtr;
	    par1  : ExprDesc;
	    par2  : ExprDesc;
	    xLab  : LabelType;
	    oTest : BOOLEAN;
	    tMode : ModeEnum;
	    pType : TypeDesc; (* type desc of par  *)
	    dType : TypeDesc; (* type desc of dest *)
	    pCls  : TyNodeClass; (* class of par   *)
	    dCls  : TyNodeClass; (* class of dest  *)
	    mId   : IdDesc;
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
	    AddOffset(bytesInWord);
	    Deref(word,NIL,unknownT);
	| minP :
	    CreateIdDesc(hMinBkt,mId,varNode);
	    PushAdr(mId,directNonL);
	    Deref(hugeInt,mId,directNonL);
	| maxP :
	    CreateIdDesc(hMaxBkt,mId,varNode);
	    PushAdr(mId,directNonL);
	    Deref(hugeInt,mId,directNonL);
	| absP :
	    PushExprValue(par1);
	    IF (pCls = doubles) THEN AbsDbl;
	    ELSIF (pCls = floats) THEN AbsFlt;
	    ELSIF (pCls = hInts) THEN 
	      AbsLong(ovfloTests IN par1^.testFlags);
	    ELSE 
	      AbsInt(ovfloTests IN par1^.testFlags);
	    END;
	| capP :
	    PushExprValue(par1);
	    Duplicate;
	    PushLit(ORD("a"));			(* val val "a" *)
	    Sub(none);				(* val exp     *)
	    PushLit(ORD("z") - ORD("a"));	(* val exp 25  *)
	    CardRelop(lessEqNode);		(* val isUpper *)
	    PushLit(ORD("a") - ORD("A"));	(* val bool 32 *)
	    Mul(none);				(* val 0or32   *)
	    Sub(none);				(* CAP(val)    *)
	| chrP :
	    PushExprValue(par1);
	    IF pCls = hInts THEN 
	      IF (ovfloTests IN par1^.testFlags) THEN
		MakeWord(intV)
	      ELSE
		MakeWord(none)
	      END;
	      pType := PointerTo(ints);
	    END;
	    IF rangeTests IN par1^.testFlags THEN
	      Test(charPtr,pType); (* dst,src *)
	    END;
	| floatP, lfloatP :		(* new code 20-6-91 kjg *)	
	    PushExprValue(par1);
	    IF pCls = subranges THEN pCls := pType^.hostType^.tyClass END;
	    IF     pCls = floats THEN FtoD;
	    ELSIF (pCls = ints)  THEN ItoD;
	    ELSIF (pCls = cards) THEN DFloat;
	    ELSIF (pCls = hInts) THEN HFloat;
	    (* ELSIF (pCls = doubles) OR (pCls = RR) THEN (* skip *)*)
	    END;
	| sfloatP :
	    PushExprValue(par1);
	    IF pCls = subranges THEN pCls := pType^.hostType^.tyClass END;
	    IF (pCls = doubles) OR (pCls = RR) THEN DtoF;
	    ELSIF pCls = ints  THEN ItoF;
	    ELSIF pCls = cards THEN FFloat;
	    ELSIF pCls = hInts THEN HFloat; DtoF;
	    (* ELSIF  pCls = floats  THEN (* skip *)*)
	    END;
	| truncP  : 
	    PushExprValue(par1);
	    IF (ovfloTests IN par1^.testFlags) THEN tMode := crdV;
	    ELSE tMode := none;
	    END;
	    IF pCls = floats THEN TruncF(tMode);
	    ELSE TruncD(tMode);
	    END;
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
	| htruncP,hentierP,hroundP : 
	    PushExprValue(par1);
	    oTest := ovfloTests IN par1^.testFlags; 
	    IF pCls = floats THEN FtoD END;
	    IF id = htruncP THEN
	      HTrunc(oTest);
	    ELSIF id = hentierP THEN
	      HEntier(oTest);
	    ELSE 
	      HRound(oTest);
	    END;
	| oddP :
	    PushExprValue(par1);
	    PushLit(1);
	    BitAND;
	| ordP : 
	    PushExprValue(par1);
	| intP : 
	    PushExprValue(par1);
	    IF ovfloTests IN par1^.testFlags THEN tMode := intV; 
	    ELSE tMode := none;
	    END;
	    IF     pCls = floats THEN TruncF(tMode)
	    ELSIF (pCls = doubles) OR (pCls = RR) THEN TruncD(tMode)
	    ELSIF  pCls = hInts  THEN MakeWord(tMode);
	    END;
	| hugeP : 
	    PushExprValue(par1);
	    oTest := ovfloTests IN par1^.testFlags; 
	    IF pCls = floats THEN
	      FtoD; HTrunc(oTest)
	    ELSIF (pCls = doubles) OR (pCls = RR) THEN
	      HTrunc(oTest)
	    ELSIF IsSignedType(pType) OR (pCls = ZZ) THEN
	      MakeIntLong;
	    ELSE
	      MakeCrdLong;
	    END;
	| valP :
	    PushExprValue(par2);
	    pType := par2^.exprType;
	    pCls  := pType^.tyClass;
	    dType := par1^.name.variable^.typType;
	    dCls  := dType^.tyClass;
	    oTest := ovfloTests IN par2^.testFlags; 
	    IF pCls = subranges THEN pCls := pType^.hostType^.tyClass END;
	    IF dCls = subranges THEN dCls := dType^.hostType^.tyClass END;
	   (*
	    *  two dimensional case analysis
	    *)
	    IF pCls = doubles THEN
	      IF dCls = doubles THEN (* skip *)
	      ELSIF dCls = floats THEN DtoF;
	      ELSE (* dest is fixed point *)
		IF dCls = ints THEN 
		  IF oTest THEN tMode := intV ELSE tMode := none END;
		  TruncD(tMode); 
	          IF rangeTests IN par2^.testFlags THEN
	            Test(dType,PointerTo(ints)); (* dst,src *)
	          END;
		ELSIF dCls = hInts THEN 
		  HTrunc(oTest); 
		ELSE 
		  IF oTest THEN tMode := crdV ELSE tMode := none END;
		  TruncD(tMode); 
	          IF rangeTests IN par2^.testFlags THEN
	            Test(dType,PointerTo(cards)); (* dst,src *)
	          END;
		END;
	      END;
	    ELSIF pCls = floats THEN
	      IF dCls = doubles THEN FtoD;
	      ELSIF dCls = floats THEN (* skip *)
	      ELSE (* dest is fixed point *)
		IF dCls = ints THEN 
		  IF oTest THEN tMode := intV ELSE tMode := none END;
		  TruncF(tMode); 
	          IF rangeTests IN par2^.testFlags THEN
	            Test(dType,PointerTo(ints)); (* dst,src *)
	          END;
		ELSIF dCls = hInts THEN 
		  FtoD; HTrunc(oTest); 
		ELSE 
		  IF oTest THEN tMode := intV ELSE tMode := none END;
		  TruncF(tMode); 
	          IF rangeTests IN par2^.testFlags THEN
	            Test(dType,PointerTo(cards)); (* dst,src *)
	          END;
		END;
	      END;
	    ELSIF pCls = ints THEN
	      IF    dCls = doubles THEN ItoD;
	      ELSIF dCls = floats  THEN ItoF;
	      ELSIF dCls = hInts   THEN MakeIntLong;
	      ELSIF rangeTests IN par2^.testFlags THEN
	        Test(dType,pType); (* dst,src *)
	      END;
	    ELSIF pCls = hInts THEN
	      IF    dCls = doubles THEN HFloat;
	      ELSIF dCls = floats  THEN HFloat; DtoF;
	      ELSIF dCls = ints    THEN
		IF oTest THEN tMode := intV ELSE tMode := none END;
		MakeWord(tMode);
		IF rangeTests IN par2^.testFlags THEN
	          Test(dType,PointerTo(ints)); (* dst,src *)
		END;
	      ELSE (* do a cardinal conversion *)
		IF oTest THEN tMode := crdV ELSE tMode := none END;
		MakeWord(tMode);
		IF rangeTests IN par2^.testFlags THEN
	          Test(dType,PointerTo(cards)); (* dst,src *)
		END;
	      END;
	    ELSE (* IF pCls = cards THEN *)
	      IF    dCls = doubles THEN DFloat;
	      ELSIF dCls = floats  THEN FFloat;
	      ELSIF dCls = hInts   THEN MakeCrdLong;
	      ELSIF rangeTests IN par2^.testFlags THEN
	        Test(dType,pType); (* dst,src *)
	      END;
	    END;  
	| lengthP : 
	    IF pCls = stringTs THEN
	      PushExprValue(par1);
	      Duplicate;
	      Deref(word,NIL,unknownT);
              AdjustParam(bytesInWord,oP1);
	      AddOffset(bytesInWord);
	      Deref(word,NIL,unknownT);
	    ELSE
	      MakeObjAndPushAdr(par1);
              AdjustParam(bytesInWord,oP1);
              PushExprValue(par2);
	    END;
            AdjustParam(bytesInWord,oP2);
	    StrLength;
	| adrP :
	    PushExprAddress(par1);
	| difAdrP : 
	    PushExprValue(par1);
	    FlattenAdr();
	    PushExprValue(par2);
	    FlattenAdr();
	    Sub(none);
	| addAdrP, subAdrP :
	    DerefDesig(par1^.name,word);
	    PushExprValue(par2);
	    IF id = addAdrP THEN
	      AddAdr();
	    ELSE 
	      NegateInt(FALSE);
	      AddAdr();
	    END;
	| timeP : 
	    PushLit(0);
            AdjustParam(bytesInWord,oP1);	(* new DEC 91 *)
	    RTSfunc(timeTrp,word,1);
	| shiftP, rotateP :
	    PushExprValue(par1);
	    PushExprValue(par2);
	    IF id = shiftP THEN Shift ELSE Rotate END;
	END;
      END CallStandardFunc;

    VAR typ : TypeDesc;

  BEGIN
      des := exp^.name;
      (*
       *  first must check here for standard procs
       *)
      IF  des.variable^.idClass = stFunc THEN
	CallStandardFunc(des.variable^.procVal);
      ELSE (* now the actual call *)
        Assert((exp^.exprType^.tyClass <> records) AND
			(exp^.exprType^.tyClass <> arrays) AND
			((exp^.exprType^.tyClass <> sets) OR
			 (exp^.exprType^.size = bytesInWord)));
	(*
	 *  for the portable version, the designator
	 *  is pushed last, after the parameters
	 *)
        IF des.variable^.idClass = varNode THEN (* proc var ... *)
	  typ := TypeOfDes(des);
	ELSE typ := des.variable^.procType;
        END;
        DoParams(typ,seq,parBytes); 
	pNum := LengthOf(seq);
        IF des.variable^.idClass = varNode THEN 
          DerefDesig(des,word);
          CallTOSFunc(parBytes,BaseObjOf(typ^.result),pNum);
	ELSE 
	  CallFunc(des.variable^.linkName, parBytes, 
		BaseObjOf(typ^.result),pNum);
	END;
      END;
  END PushFunctionValue;

  PROCEDURE AssignFuncResult(exp : ExprDesc;
			     pop : BOOLEAN);
  (* pre :  destination  address is on top of stack *)
  (* post:  (pop = FALSE) ==> dst address still tos *)

    VAR parBytes : INTEGER;
	pNum	 : CARDINAL;
        des      : DesigRec;
        typ      : TypeDesc;

  BEGIN
    des := exp^.name;
    Assert((exp^.exprType^.tyClass = records) OR
              (exp^.exprType^.tyClass = arrays) OR
		((exp^.exprType^.tyClass = sets) AND
		(exp^.exprType^.size <> bytesInWord)));
    (*
     *  for the portable version, the designator
     *  is pushed last, after the parameters
     *
     *  First, some pesky preliminaries ... is it a castP ?
     *  if so, the assign becomes a null operation since 
     *  the pushed address will be the actual object location
     *  rather than the address of the function result temp.
     *)
    IF des.variable^.idClass = varNode THEN (* a proc var ... *)
      typ := TypeOfDes(des);
    ELSE typ := des.variable^.procType;
    END;
    DoParams(typ,exp^.paramSeq,parBytes); 
    pNum := LengthOf(exp^.paramSeq) + 1; 	(* ADD 1 FOR DST PTR *)
(*
 *  value is top of stack again ...
 *  PushMemTmp(exp^.sourceLoc.pos);
 *	does not work for interpreter code!
 *)
    MakeDstPointer(exp^.exprType^.size,exp^.exprType^.tyClass = records); 
    IF des.variable^.idClass = varNode THEN 
      DerefDesig(des,word);
      IF NOT pop THEN
	CallTOSFunc(parBytes,word,pNum);
      ELSE CallTOSProc(parBytes,pNum);	(* call as a procedure !!! *)
      END;
    ELSE 
      IF NOT pop THEN
	CallFunc(des.variable^.linkName, parBytes, word,pNum);
      ELSE CallProc(des.variable^.linkName,parBytes,pNum); (*  proc !!! *)
      END;
    END;
  END AssignFuncResult;

  PROCEDURE PushLongValue(op : ExprDesc);
  BEGIN
    PushExprValue(op);
    IF op^.exprClass = literalNode THEN
      IF op^.exprType^.tyClass = UU THEN MakeCrdLong ELSE MakeIntLong END;
    END;
  END PushLongValue;

  PROCEDURE PushExprValue(exp : ExprDesc);
  (* pre  : exp^ is a word sized or less object, or a REAL *)
    VAR tLab, fLab (*, xLab*) : LabelType;
	class  : TyNodeClass;
	sClass : TyNodeClass;
        objt   : Object;
	size   : CARDINAL;
	sSize  : CARDINAL;
	(* fiIx  : CARDINAL; *)
	tix    : TempIndex;
        dType  : TypeDesc;
	set    : LexAttType;
	litValue : CARDINAL;
	sign, doTest, lit, isAdr : BOOLEAN;
  BEGIN
    WITH exp^ DO
      class := exprType^.tyClass;	(* not always what is needed *)
      CASE exprClass OF
      | preconNode :
	  StatementSeq(evalLst,0);
	  PushExprValue(exp^.theCall);
      | selConstNode : 
	  ConstDesignator(exp); 
	  objt := BaseObjOf(exprType);
	  Deref(objt,NIL,invariant);
      | adrDesigNode : 
	  Designator(name); 
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
            dType := TypeOfDes(name);
            class := dType^.tyClass; 
	    objt  := BaseObjOf(dType);
	    DerefDesig(name,objt); 
	  ELSE
	    Designator(name); 
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
	  IF NeedsCopy(sClass,sSize) THEN
	    IF needTmp THEN
(*
 *	StdError.WriteString("21 BlkCp in, deref out of temp" + 12C);
 *)
	      PushAdr(tempId,directLocl);
	      Duplicate;
              MakeObjAndPushAdr(source);
	      IF sClass <> SS THEN
                PushLit(sSize);				(* source size *)
	      ELSIF source^.conValue.strHigh >= exprType^.size THEN
                PushLit(exprType^.size);		(* dest size   *)
	      ELSE
                PushLit(source^.conValue.strHigh + 1);  (* string size *)
	      END;
	      CopyBlock(source^.exprType^.alignMask);
	    ELSE
(*
 *	StdError.WriteString("22 Deref of source address, no temp" + 12C);
 *)
              MakeObjAndPushAdr(source);
	    END;
	    Deref(BaseObjOf(exprType),NIL,unknownT);
	  ELSE
	    PushExprValue(source);
	    IF needTmp THEN
	      PushAdr(tempId,directLocl);
	      IF wrd2wrd THEN 
(*
 * StdError.WriteString("24 Assign dType, deref dType out of temp" + 12C);
 *)
	        Assign(BaseObjOf(exprType),tempId,directLocl);
	      ELSE 
(*
 * StdError.WriteString("23 Assign sType, deref dType out of temp" + 12C);
 *)
	        Assign(BaseObjOf(source^.exprType),tempId,directLocl);
	      END;
	      PushAdr(tempId,directLocl);
	      Deref(BaseObjOf(exprType),tempId,directLocl);
	    (* ELSE do nothing *)
(*
 *	ELSE StdError.WriteString("25 Do nothing at all" + 12C);
 *)
	    END;
	  END;
      | funcDesigNode :
	  PushFunctionValue(exp,paramSeq);
      | setDesigNode :
	  WordSetConstructor(exp);
      | literalNode : 
	  IF (class = chars) OR
	     (class = S1) THEN 
	    PushLit(ORD(conValue.charValue));
	  ELSIF class = sets THEN (* assert: word set *)
	    FOR size := 0 TO bytesInWord - 1 DO
	      IF bigEndian THEN
	        set.bytes[bytesInWord - 1 - size] :=
				StringTable(conValue.patternIx + size);
	      ELSE
	        set.bytes[size] := StringTable(conValue.patternIx + size);
	      END;
	    END;
	    PushLit(set.fixValue);
	  ELSIF class = RR THEN
	    IF rtOffset = literalZero THEN
	      PushLit(0); ItoD;
	    ELSE
	      PushCon(rtOffset);		(* float's done explicitly *)
	      Deref(double,NIL,invariant);	(* and don't come here     *)
	    END;
	  ELSE PushLit(conValue.intValue);
 	  END;
      | negateNode :
	  PushExprValue(notOp);
	  IF (class = doubles) THEN NegateDbl;
	  ELSIF (class = floats) THEN NegateFlt;
	  ELSIF (class = hInts)  THEN 
	    IF notOp^.exprClass = literalNode THEN MakeIntLong END;
	    NegateLong(ovfloTests IN testFlags);
	  ELSE NegateInt(ovfloTests IN testFlags);
	  END;
      | inNode :
	  tix  := sourceLoc.pos; (* frontend temporary *)
	  size := rightOp^.exprType^.size;
	 (*
	  *  note the use of unsigned tests here to catch
	  *  (perhaps) signed values which are at either 
	  *  end of the range of the base type of the set.
	  *)
	  IF leftOp^.exprClass = literalNode THEN
	    litValue := leftOp^.conValue.fixValue;
	    IF litValue > MaxOfOrdType(rightOp^.exprType^.baseType) THEN
	      PushLit(0);
	    ELSE
	      IF size <= bytesInWord THEN
		PushExprValue(rightOp);
	      ELSE
	        BuildBigSet(rightOp,size DIV bytesInWord);
  	        PushExprAddress(rightOp);
	        IF litValue >= bitsInWord THEN
	          AddOffset((litValue DIV bitsInWord) * bytesInWord);
	        END;
	        Deref(word,NIL,unknownT);
	      END;
	      PushLit(litValue MOD bitsInWord);
	      SetInOp;
	    END;
	  ELSIF (rangeTests IN leftOp^.testFlags) THEN
	   (*
	    *  It is the left operand which carries the information
	    *  as to whether an out of range left operand can occur
	    *)
	    PushExprValue(leftOp);
	    MakeTemp(tix);
	    PushLit(MaxOfOrdType(rightOp^.exprType^.baseType));
	    CardRelop(lessEqNode);      (* true ==> in range *)
	    IF size <= bytesInWord THEN (* a word sized set  *)
	      PushExprValue(rightOp);   (* rhs *)
	      PushTmp(tix);		(* lhs *)
	    ELSE
	      NegateInt(FALSE);		(* turn true/false into 111.../000...*)
	      Duplicate;
	      PushTmp(tix);		(* lhs *)
	      BitAND;
	      MakeTemp(tix); 
	      PopNDiscard;
	     (*
	      *  the temporary now has an in-range index or zero
	      *)
	      BuildBigSet(rightOp,size DIV bytesInWord);
  	      PushExprAddress(rightOp);
	      PushTmp(tix);		(* modified index *)
	      PushLit(bitsInWord);  Div(crdV);
	      PushLit(bytesInWord); Mul(none); (* == lOp DIV 32 * 4 *)
	      AddAdr();
	      Deref(word,NIL,unknownT);
	      PushTmp(tix);		(* modified index *)
	      PushLit(bitsInWord - 1); BitAND;	      (* == lOp MOD 32 *)
	    END;
	    SetInOp;
	    BitAND;
	  ELSE (* variable lhs, but no range test... *)
	    IF size <= bytesInWord THEN
	      PushExprValue(rightOp);   (* rhs *)
	      PushExprValue(leftOp);    (* lhs *)
	    ELSE
	      BuildBigSet(rightOp,size DIV bytesInWord);
  	      PushExprAddress(rightOp);		(* construct set   23-7-91 *)
	      PushExprValue(leftOp);
	      MakeTemp(tix);
	      PushLit(bitsInWord);  Div(crdV);
	      PushLit(bytesInWord); Mul(none); (* == lOp DIV 32 * 4 *)
	      AddAdr();
	      Deref(word,NIL,unknownT);
	      PushTmp(tix);
	      PushLit(bitsInWord - 1); BitAND;	    (* == lOp MOD 32 *)
	    END;
	    SetInOp;
	  END;
      | equalsNode .. lessEqNode :
	  (* sub exps are not necessarily word sized *)
	  IF rightOp^.exprType^.tyClass = sets THEN
	    size := rightOp^.exprType^.size;
	    IF size > bytesInWord THEN (* big set *)
	      BuildBigSet(leftOp,size DIV bytesInWord);
	      BuildBigSet(rightOp,size DIV bytesInWord);
              PushLit(size DIV bytesInWord);
	      AdjustParam(bytesInWord,oP3); (* new Dec 91 *)
	      PushExprAddress(rightOp);
	      AdjustParam(bytesInWord,oP2); (* new Dec 91 *)
	      PushExprAddress(leftOp);
	      AdjustParam(bytesInWord,oP1); (* new Dec 91 *)
	      BigSetRelop(exprClass);
	    ELSE (* a word-sized set *)
	      PushExprValue(leftOp);
	      PushExprValue(rightOp);
	      SetRelop(exprClass);
	    END;
	  ELSE (* not a set *)
	    (* find class of _operands_ *)
	    class  := leftOp^.exprType^.tyClass;
	    sClass := rightOp^.exprType^.tyClass;
	    isAdr  := ((class = adrs) OR (class = pointers)) AND 
		      (rightOp^.exprClass <> literalNode) AND
		      (leftOp^.exprClass <> literalNode);
	    IF (class = RR) AND (rightOp^.exprType^.tyClass = floats) THEN
	      PushFloatConst(leftOp);		(* jl Jun 94 *)
	      class := floats;
	    ELSIF (class = hInts) OR (sClass = hInts) THEN
	      PushLongValue(leftOp);
	    ELSE 
	      PushExprValue(leftOp);
	      IF isAdr THEN FlattenAdr() END;
	    END;
	    IF (class = floats) AND (rightOp^.exprType^.tyClass = RR) THEN
	      PushFloatConst(rightOp);		(* jl Jun 94 *)
	    ELSIF (class = hInts) OR (sClass = hInts) THEN
	      PushLongValue(rightOp);
	    ELSE 
	      PushExprValue(rightOp);
	      IF isAdr THEN FlattenAdr() END;
	    END;
	    IF  (class = doubles) OR (class = RR) THEN
	      RealRelop(exprClass);
	    ELSIF (class = floats) THEN
	      SRealRelop(exprClass);
	    ELSIF (class = hInts) OR (sClass = hInts) THEN
	      HugeRelop(exprClass);
	    ELSIF (leftOp^.exprClass <> literalNode) AND
		   IsSignedType(leftOp^.exprType) OR
	    	  IsSignedType(rightOp^.exprType) THEN (* kjg jan 93 *)
	      IntRelop(exprClass);
	    ELSE CardRelop(exprClass);
	    END;
	  END;
      | andNode :
	    AllocateLabel(fLab);
	    BoolJump(leftOp,fLab,fallThrough);
	    BoolJump(rightOp,fLab,fallThrough);
            PushBool(fLab,fallThrough,mergeId);
      | orNode :
	    AllocateLabel(tLab);
	    BoolJump(leftOp,fallThrough,tLab);
	    BoolJump(rightOp,fallThrough,tLab);
            PushBool(fallThrough,tLab,mergeId);
      | notNode : 
	  CASE notOp^.exprClass OF
	  | notNode : PushExprValue(notOp^.notOp);
          | andNode :
	      AllocateLabel(fLab);
	      BoolJump(notOp^.leftOp,fLab,fallThrough);
	      BoolJump(notOp^.rightOp,fLab,fallThrough);
              PushBool(fallThrough,fLab,notOp^.mergeId);
          | orNode :
	      AllocateLabel(tLab);
	      BoolJump(notOp^.leftOp,fallThrough,tLab);
	      BoolJump(notOp^.rightOp,fallThrough,tLab);
              PushBool(tLab,fallThrough,notOp^.mergeId);
	  ELSE
	    PushExprValue(notOp);
	    NegateBool;
	  END;
      ELSE (* is a binop *)
	IF class = floats THEN		(* new code 20-6-91 kjg *)
	  IF leftOp^.exprClass = literalNode THEN (* shorten *)
	    PushFloatConst(leftOp);		(* jl Jun 94 *)
	  ELSE
	    PushExprValue(leftOp);
	  END;
	  IF rightOp^.exprClass = literalNode THEN (* shorten *)
	    PushFloatConst(rightOp);		(* jl Jun 94 *)
	  ELSE
	    PushExprValue(rightOp);
	  END;
	  CASE exprClass OF
          | starNode :  MulFlt;
	  | plusNode :  AddFlt;
	  | minusNode : SubFlt;
	  | slashNode : SlashFlt;
          END;
	ELSIF class = doubles THEN
          PushExprValue(leftOp);
          PushExprValue(rightOp);
	  CASE exprClass OF
          | starNode :  MulDbl;
	  | plusNode :  AddDbl;
	  | minusNode : SubDbl;
	  | slashNode : SlashDbl;
          END;
	ELSIF exprType^.tyClass = hInts THEN
	 (*
	  *  for the moment, literals are word-size
	  *  and must be explicitly widened.
	  *)
          PushLongValue(leftOp);
          PushLongValue(rightOp);
	  doTest := (ovfloTests IN testFlags);
	  CASE exprClass OF
          | starNode    : MulLong(doTest);
	  | plusNode    : AddLong(doTest);
	  | minusNode   : SubLong(doTest);
	  | slashNode   : SlashLong;
	  | remNode     : RemLong;
	  | divNode     : DivLong;
	  | modulusNode : ModLong;
	  END;
	ELSE
          PushExprValue(leftOp);
          PushExprValue(rightOp);
	  IF exprType^.tyClass = sets THEN
	    Assert(exprType^.size = bytesInWord);
	    CASE exprClass OF 
	    | plusNode  : BitOR;
            | starNode  : BitAND;
	    | slashNode : BitXOR;
	    | minusNode : BitNegate; BitAND;
            END;
	  ELSE
	    doTest := (ovfloTests IN testFlags);
	    sign := IsSignedType(exprType);
	    CASE exprClass OF
            | starNode    : Mul(addMode[sign,doTest]);
	    | plusNode    : Add(addMode[sign,doTest]);
	    | minusNode   : Sub(addMode[sign,doTest]);
	    | remNode     : Rem(divMode[sign,doTest]);
	    | slashNode   : Slash(divMode[sign,doTest]);
	    | divNode, modulusNode : 
		IF doTest AND sign AND 
		   (rightOp^.exprClass <> literalNode) THEN ModTest() END;
		IF exprClass = divNode THEN 
		  Div(divMode[sign,doTest]);
		ELSE 
		  Mod(divMode[sign,doTest]);
		END;
            END;
	  END;
        END;
      END; (* outer case *)
    END; (* with *)
  END PushExprValue;

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
			  tmp   : CARDINAL;		(* temporary indes   *)
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
	  PushTmp(tmp);				(*     [min---max]       *)
	  PushLit(min);
	  IF sng THEN (* singleton *)
	    CardRelop(equalsNode);
	  ELSE (* a range *)
	    Sub(none); PushLit(max-min);
	    CardRelop(lessEqNode);
	  END;
	  BranchTrue(nxt);
	ELSIF tMin < min THEN			(* [tMin-----------tMax] *)
	  PushTmp(tmp);				(*           [min---max] *)
	  PushLit(min);
	  IF sng THEN CardRelop(equalsNode) ELSE IntRelop(grEqualNode) END;
	  BranchTrue(nxt);
	  tMax := min - 1;
	ELSIF max < tMax THEN			(* [tMin-----------tMax] *)
	  PushTmp(tmp);				(* [min---max]           *)
	  PushLit(max);
	  IF sng THEN CardRelop(equalsNode) ELSE IntRelop(lessEqNode) END;
	  BranchTrue(nxt);
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
			 tmp   : CARDINAL;
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
      PushTmp(tmp);
      mnVal := str[lo].min;
     (*
      *  generate the jump code
      *)
      tbSiz := str[hi].max - mnVal + 1;
      CreateJumpTable(tbSiz,tbPtr);
      IF mnVal <> 0 THEN
	PushLit(mnVal);
	Sub(none);
      END;
      Switch(tbPtr^.locn);
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
      EmitJumpTable(tbPtr,0);
    END DoDispatch;

    PROCEDURE PartTests(str   : CaseString;	(* the cases string    *)
			prt   : PartString;	(* the partition str.  *)
			lo,hi : INTEGER;	(* range of part. tab. *)
			tyMin : INTEGER;	(* value range minimum *)
			tyMax : INTEGER;	(* value range maximum *)
			tmp   : CARDINAL;	(* index of temp value *)
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
      IF lo < mid THEN AllocateLabel(loLab) ELSE loLab := def END;
      IF mid < hi THEN AllocateLabel(hiLab) ELSE hiLab := def END;
      IF (loLab = hiLab) AND
	 (mnVal > tyMin) AND 
	 (mxVal < tyMax) THEN   (* optimize dbl-ended *)
	PushTmp(tmp);
	IF mnVal = mxVal THEN   (* equality test here *)
	  PushLit(mnVal);
	  CardRelop(notEqNode);
	ELSE
	  IF mnVal <> 0 THEN PushLit(mnVal); Sub(none) END;
	  PushLit(mxVal - mnVal);  (* lit <> 0! *)
	  CardRelop(greaterNode);
	END;
	BranchTrue(loLab);
      ELSE
	IF mnVal > tyMin THEN (* test for low bound *)
          PushTmp(tmp);
          PushLit(mnVal);
          IntRelop(lessNode);
          BranchTrue(loLab);
	END;
	IF mxVal < tyMax THEN (* test for high bound *)
          PushTmp(tmp);
          PushLit(mxVal);
          IntRelop(greaterNode);
          BranchTrue(hiLab);
	END;
      END;
      (* now do this partition *)
      IF maxIx = minIx THEN			(* singleton range only *)
	Branch(str[maxIx].cas^.theLabel);
      ELSIF maxIx - minIx < linMax THEN
	LinearTests(str,minIx,maxIx,mnVal,mxVal,tmp,def);
      ELSE
	DoDispatch(str,minIx,maxIx,tmp,def);	(* with no bounds check *)
      END;
      (* now emit the others recursively *)
      IF lo < mid THEN
	Assert(mnVal > tyMin);
	CodeLabel(loLab); PartTests(str,prt,lo,mid-1,tyMin,(mnVal-1),tmp,def);
      END;
      IF mid < hi THEN
	Assert(mxVal < tyMax);
	CodeLabel(hiLab); PartTests(str,prt,mid+1,hi,(mxVal+1),tyMax,tmp,def);
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
    BEGIN
(* *$T- all arithmetic modulo 2**32 *)
      WITH stat^ DO
       (*
	*  Assert: selector consts are all in the integer range.
	*
	*  Allocate some labels.
	*)
	AllocateLabel(exitLabel);
	AllocateLabel(defLabel);
	InitCursor(cases,casCurs);
	WHILE NOT Ended(casCurs) DO
	  GetNext(casCurs,thisCase);
	  AllocateLabel(location);
	  thisCase^.theLabel := location;
	END;
	selTmp := stat^.sourceLoc.pos; (* ugly kludge ... *)
	PushExprValue(caseInfo^.switch);
	MakeTemp(selTmp);
	PopNDiscard;
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
	InitCursor(cases,casCurs);
	WHILE NOT Ended(casCurs) DO
	  GetNext(casCurs,thisCase);
	  CodeLabel(thisCase^.theLabel);
	  StatementSeq(thisCase^.statSeq,lab);
	  Branch(exitLabel);
	END;
       (*
	*  emit the default code
	*)
        CodeLabel(defLabel);
	IF IsEmpty(default) THEN 
	  PushTmp(selTmp);
          AdjustParam(bytesInWord,oP1); (* new DEC 91 *)
	  Trap(m2_casTrp,1);
	ELSE 
          StatementSeq(default,lab);
	END;
	CodeLabel(exitLabel);
      END;
(* *$T= end arithmetic modulo 2**32 *)
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

      PROCEDURE Highest(exp : ExprDesc) : CARDINAL;
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
      END Highest;

      PROCEDURE Lowest(exp : ExprDesc) : CARDINAL;
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
      END Lowest;

      VAR eLab : LabelType;	(* loop entry label *)
	  once : BOOLEAN;

    BEGIN
      AllocateLabel(lLab);
      AllocateLabel(xLab);
      AllocateLabel(eLab);
      WITH stat^ DO
        posStp := stepSize > 0;
	hard   := (initial^.exprClass <> literalNode) OR
			(final^.exprClass <> literalNode);
        (*
         * ALL limits and test are based on "int" or "unsigned"
         *)
        cvTyp := controlVariable^.varType;
	cvObj := BaseObjOf(cvTyp);
	base  := BaseTypeOf(cvTyp);

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
	finalHigh.crd := Highest(final);
	finalLow.crd  := Lowest(final);
	initHigh.crd  := Highest(initial);
	initLow.crd   := Lowest(initial);
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
	  iniExp := stat^.sourceLoc.pos; (* ugly kludge ... *)
	  finExp := iniExp + bytesInWord;

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
	    PushLit(absStep);
	    Div(crdV);		(* unsigned divide *)
	  END;
         (*
	  *  Top of the abstract stack is now the 
	  *  required number of loop iterations
	  *)
	  PushAdr(countDownVar,directLocl); 
	  Assign(word,countDownVar,directLocl);
	END;
       (* $T- *)
	once := NOT hard AND 
			(ABS(finalHigh.int - initHigh.int) DIV absStep = 0);
       (* $T= *)
       (*
	*  Now do the pretest if required ...
	*  Note that if not hard, then no test.
	*)
	IF preTst AND hard THEN
	  PushTmp(iniExp);
	  PushTmp(finExp);
	  IF posStp THEN
	    (* test if initial > final, and so on*)
	    IF signed THEN IntRelop(greaterNode);
	    ELSE CardRelop(greaterNode);
	    END;
	  ELSIF signed THEN IntRelop(lessNode);
	  ELSE CardRelop(lessNode);
	  END;
	 (*
	  *  jump over loop 
	  *)
	  BranchTrue(xLab);
	END; (* if preTst *)
       (*
	*  Now assign the starting value ...
	*)
	IF hard THEN PushTmp(iniExp) ELSE PushLit(initHigh.int) END;
	PushAdr(controlVariable,directLocl);
	Assign(cvObj,controlVariable,directLocl);

	IF once THEN StatementSeq(forBody,lab); RETURN END;

	Branch(eLab);
       (*
	*  Now start the loop body ...
	*)
	LoopLabel(lLab);
       (*
	*  now adjust the control variable (if no range check)
	*)
	PushAdr(controlVariable,directLocl);
	Duplicate;
	Deref(cvObj,controlVariable,directLocl);
	PushLit(stepSize);
	Add(none);
	IF rangeTests IN final^.testFlags THEN
	  Test(cvTyp,final^.exprType);
	END;
	ReverseAssign(cvObj,controlVariable,directLocl);
       (*
  	*  Now adjust the iteration count.
	*)
	IF hard THEN (* decrement *)
	  PushAdr(countDownVar,directLocl);
	  Deref(word,countDownVar,directLocl);
	  PushLit(1);
	  Sub(none);
	  PushAdr(countDownVar,directLocl);
	  Assign(word,countDownVar,directLocl);
	END;
       (*
	*  now emit the loop body
	*)
	CodeLabel(eLab);
        StatementSeq(forBody,lab);
       (*
	*  now do the termination test ...
	*)
	IF hard THEN (* decrement *)
	  PushAdr(countDownVar,directLocl);
	  Deref(word,countDownVar,directLocl);
	  BranchTrue(lLab);
	ELSE
	  PushAdr(controlVariable,directLocl);
	  Deref(cvObj,controlVariable,directLocl);
	 (* $T- *) (* $R- *)
	  PushLit(finalHigh.int - stepSize);
	  IF posStp THEN
	    IF signed THEN 
	      IntRelop(greaterNode);
	    ELSE 
	      CardRelop(greaterNode);
	    END;
	  ELSE
	    IF signed THEN 
	      IntRelop(lessNode);
	    ELSE 
	      CardRelop(lessNode);
	    END;
	  END;
	 (* $T= *) (* $R= *)
	  BranchFalse(lLab);
	END;
	LoopEnd(lLab);
	IF preTst THEN CodeLabel(xLab) END;
      END; (* with *)
    END EncodeFor;
   (* ============================================================ *)

    PROCEDURE NewEncodeIf(stat : StatDesc);
      TYPE DefBlock = POINTER TO RECORD
			label  : LabelType;
			branch : IfDesc;
		      END;
      VAR xLab : LabelType; (* the exit label *)
	  cursor : ElemPtr;
	  elemnt : IfDesc;
	  deferB : DefBlock;
	  blocks : Sequence; (* of DefBlocks *)
    BEGIN
      AllocateLabel(xLab);
      InitSequence(blocks);
      InitCursor(stat^.branches,cursor);
      WHILE NOT NextIsLast(cursor) DO
	NEW(deferB);
	WITH deferB^ DO
	  AllocateLabel(label);
	  GetNext(cursor,branch);
	  BoolJump(branch^.condition,fallThrough,label);
	END;
	LinkLeft(blocks,deferB);
      END;
      GetNext(cursor,elemnt);
      WITH elemnt^ DO
	IF condition <> NIL THEN (* ==> no elsepart *)
	  BoolJump(condition,xLab,fallThrough);
	END;
	StatementSeq(statSeq,lab);
      END;
      IF NOT IsEmpty(blocks) THEN 
        Branch(xLab); (* and now spill blocks *)
        InitCursor(blocks,cursor);
        WHILE NOT NextIsLast(cursor) DO
	  GetNext(cursor,deferB);
	  CodeLabel(deferB^.label);
	  StatementSeq(deferB^.branch^.statSeq,lab);
	  Branch(xLab);
	END;
	GetNext(cursor,deferB);
	CodeLabel(deferB^.label);
	StatementSeq(deferB^.branch^.statSeq,lab); (* and fall through *)
	DisposeList(blocks);
      END;
      CodeLabel(xLab);
    END NewEncodeIf;

    PROCEDURE OldEncodeIf(stat : StatDesc);
      VAR xLab : LabelType; (* the exit label *)
	  tLab : LabelType; (* the true label *)
	  fLab : LabelType; (* the false label *)
	  cursor : ElemPtr;
	  branch : IfDesc;
    BEGIN
      AllocateLabel(xLab);
      InitCursor(stat^.branches,cursor);
      WHILE NOT NextIsLast(cursor) DO
	GetNext(cursor,branch);
	AllocateLabel(fLab);
	WITH branch^ DO
	  Assert(condition <> NIL);
	  BoolJump(condition,fLab,fallThrough);
	  StatementSeq(statSeq,lab);
	END;
 	Branch(xLab);
	CodeLabel(fLab);
      END;
      GetNext(cursor,branch);
      WITH branch^ DO
	IF condition <> NIL THEN (* ==> no elsepart *)
	  BoolJump(condition,xLab,fallThrough);
	END;
	StatementSeq(statSeq,lab);
      END;
      CodeLabel(xLab);
    END OldEncodeIf;

    PROCEDURE WriteProcCall(stat : StatDesc);

      VAR parBytes : INTEGER;
	  seq      : Sequence;

      PROCEDURE CallStandardProc(id : StandardProcs);
	VAR curs : ElemPtr;
	    par1 : ExprDesc;
	    par2 : ExprDesc;
	    next : ExprDesc;
	    pSiz : CARDINAL;
	    xLab : LabelType;
	    sign : BOOLEAN;
	    test : BOOLEAN;
	    mode : ModeEnum;
	    pType : TypeDesc; (* type desc of par1 *)
	    class : TyNodeClass;
 	    objct : Object;
	    dVar  : IdDesc;
	    dMod  : AccessMode;
	    uTmp,vTmp,wTmp,xTmp  : TempIndex;
	    pName : HashBucketType;
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
	| newP, disP : 
	   (*
	    * layout of stringtype is ...
	    *
	    *    ptr	     blk	   mem
	    *   [===] ---> +-----+
	    *              |    -+-----> +-----+
	    *              | hi  |       |     | num * size
	    *              | num |       |     |
	    *              +-----+       v     v
	    *)
	    IF par2 = NIL THEN RETURN END;
	    IF parsFixed THEN pSiz := 0 ELSE pSiz := 2 * bytesInWord END;
	    IF id = newP THEN (* new(var,num,alloc) *)
	      uTmp := stat^.sourceLoc.pos;
	      vTmp := uTmp + bytesInWord;
	      GetNext(curs,next);  (* alloc *)
	      PushDesig(par1^.name,dVar,dMod);
	      MakeTemp(uTmp);			(* -|,var		*)
	     (*
	      *  Call allocate for descriptor block 
	      *)
              AdjustParam(bytesInWord,oP1);
	      PushLit(3 * bytesInWord);		(* -|,12		*)
              AdjustParam(bytesInWord,oP2);
	      CallProc(next^.name.variable^.linkName, pSiz, 2);
	     (*
	      *  Fill in the high = -1 at word-offset
	      *)
	      PushLit(-1);			(* -|,-1		*)
	      PushTmp(uTmp);			(* -|,-1,var		*)
	      Deref(word,dVar,dMod);		(* -|,-1,blk		*)
	      MakeTemp(uTmp);
	      AddOffset(bytesInWord);		(* -|,-1,blk+4		*)
	      Assign(word,NIL,unknownT);	(* -|			*)
	     (*
	      *  Fill in the limit at 2 * word-offset
	      *)
	      PushExprValue(par2); (* numEl *)
	      MakeTemp(vTmp);
	      PushTmp(uTmp);			(* -|,num,blk		*)
	      AddOffset(2 * bytesInWord);	(* -|,num,blk+8		*)
	      Assign(word,NIL,unknownT);	(* -|			*)
	     (*
	      *  Now to allocate the variable block
	      *)
	      PushTmp(vTmp);			(* -|,num		*)
	      IF par1^.exprType^.targetType^.size > 1 THEN
	        PushLit(par1^.exprType^.targetType^.size);
	        Mul(none);			(* -| num*siz		*)
	      END;
              AdjustParam(bytesInWord,oP2);     (* -|			*)
	      PushTmp(uTmp);			(* -|,blk		*)
              AdjustParam(bytesInWord,oP1);
	      CallProc(next^.name.variable^.linkName, pSiz, 2);
	    ELSE
	      PushDesig(par1^.name,dVar,dMod);
	      Duplicate;
	      Deref(word,dVar,dMod);		(* -|,ptr,blk		*)
	      Duplicate; 			(* -|,ptr,blk,blk	*)
	      AddOffset(2 * bytesInWord);	(* -|,ptr,blk,blk+8	*)
	      Deref(word,NIL,unknownT);		(* -|,ptr,blk,lim	*)
	      PushLit(par1^.exprType^.targetType^.size);
	      Mul(none);			(* -| ptr,blk,lim*siz	*)
              AdjustParam(bytesInWord,oP2);	(* -|,ptr,blk		*)
              AdjustParam(bytesInWord,oP1); 	(* -|,ptr		*)
	      CallProc(par2^.name.variable^.linkName, pSiz, 2);
              AdjustParam(bytesInWord,oP1);	(* -|			*)
	      PushLit(3 * bytesInWord);		(* -|,12		*)
              AdjustParam(bytesInWord,oP2);	(* -|			*)
	      CallProc(par2^.name.variable^.linkName, pSiz, 2);
	    END;
	| resetP :
	    PushExprValue(par1);		(* -|,blk		*)
	    AddOffset(bytesInWord);		(* -|,&hi		*)
	    IF rangeTests IN par2^.testFlags THEN 
	      uTmp := stat^.sourceLoc.pos;
	      Duplicate; 			(* -|,&hi,&hi		*)
	      Deref(word,NIL,unknownT);		(* -|,&hi,hi		*)
	      MakeTemp(uTmp); PopNDiscard;	(* -|,&hi		*)
	      PushExprValue(par2);		(* -|,&hi,new		*)
	      VariableCheck(uTmp,-1);
	    ELSE
	      PushExprValue(par2);		(* -|,&hi,new		*)
	    END;
	    ReverseAssign(word,NIL,unknownT);	(* -|			*)
	| appendP :
	    AllocateLabel(xLab);
	    uTmp := stat^.sourceLoc.pos;	(* blk adr  *)
	    vTmp := uTmp + bytesInWord;		(* inc len  *)
	    wTmp := vTmp + bytesInWord;		(* blk2 adr *)
	    xTmp := wTmp + bytesInWord;		(* blk2 adr *)
	    IF parsFixed THEN pSiz := 0 ELSE pSiz := 4 * bytesInWord END;
	    PushExprValue(par1);		(* -|,blk		*)
(*u+*)	    MakeTemp(uTmp);			(* -|,blk		*)
	    AddOffset(bytesInWord);		(* -|,b+4		*)
	    Deref(word,NIL,unknownT);		(* -|,hi1		*)
(*x+*)	    MakeTemp(xTmp);			(* -|,hi1		*)
	   (*
	    *  Get the length increment for each case and
	    *  add it to high to get new high. Assign this.
	    *)
	    IF stat^.appendClass = 0 THEN	(* stringTs *)
	      PushExprValue(par2);		(* -|,blk2		*)
(*w+*)	      MakeTemp(wTmp);
	      AddOffset(bytesInWord);		(* -|,b2+4		*)
	      Deref(word,NIL,unknownT);		(* -|,hi2		*)
	      PushLit(1);
	      Add(none);
	    ELSIF stat^.appendClass = 1 THEN	(* arrays *)
	      IF par2^.exprType^.isDynamic THEN
		Assert(par2^.exprClass = desigNode);
		PushOpenCount(par2);
	      ELSE					(* element *)
		PushLit(IndexCardinality(par2^.exprType));
	      END;
	    ELSE
	      PushLit(1);
	    END;
(*v+*)	    MakeTemp(vTmp);
	    Add(none);				(* -|,nHi		*)
	    Duplicate;				(* -|,nHi,nHi		*)
	    PushTmp(uTmp);			(* -|,nHi,nHi,blk	*)
	    AddOffset(bytesInWord);		(* -|,nHi,nHi,b+4	*)
	    Assign(word,NIL,unknownT);		(* -|,nHi		*)
	   (*
	    *  Check if this equals the limit ...
	    *)
	    PushTmp(uTmp);			(* -|,nHi,blk		*)
	    AddOffset(bytesInWord * 2);		(* -|,nHi,b+8		*)
	    Deref(word,NIL,unknownT);		(* -|,nHi,num		*)
	    IntRelop(lessNode);			(* -|,bool		*)
	    BranchTrue(xLab);
	   (*
	    *  If the limit is broken, then call
	    *  __XPNDSTR__(str,elSiz,alloc,deall);
	    *)
	    PushTmp(uTmp);
	    AdjustParam(bytesInWord,oP1); 
	    PushLit(par1^.exprType^.targetType^.size);
	    AdjustParam(bytesInWord,oP2); 
	    GetNext(curs,next); Designator(next^.name);
	    AdjustParam(bytesInWord,oP3); (* alloc *)
	    GetNext(curs,next); Designator(next^.name);
	    AdjustParam(bytesInWord,oP4); (* deall *)
	    CallProc(xpndBkt, pSiz, 4);

	    CodeLabel(xLab);
	   (*
	    *  Now append the elements ...
	    *)
(*u-*)	    PushTmp(uTmp);			(* -|,blk		*)
	    Deref(word,NIL,unknownT);		(* -|,mem		*)
(*x-*)	    PushTmp(xTmp);			(* -|,mem,hi1		*)
	    PushLit(1); Add(none);
	    IF par1^.exprType^.targetType^.size > 1 THEN
	      PushLit(par1^.exprType^.targetType^.size);
	      Mul(none);
	    END;
	    AddAdr;				(* -|,dst		*)
	   (* case 1: STR + STR *)
	    IF stat^.appendClass = 0 THEN
(*w-*)	      PushTmp(wTmp);
	      Deref(word,NIL,unknownT);		(* -|,dst,src		*)
	      PushTmp(vTmp);
	      IF par1^.exprType^.targetType^.size > 1 THEN
	        PushLit(par1^.exprType^.targetType^.size);
		Mul(none);
	      END;				(* -|,dst,src,siz	*)
	      CopyBlock(par1^.exprType^.targetType^.alignMask);
	   (* case 2: STR + ARR *)
	    ELSIF stat^.appendClass = 1 THEN
	      MakeObjAndPushAdr(par2);		(* -|,dst,src		*)
(*v-*)	      PushTmp(vTmp);
	      IF par1^.exprType^.targetType^.size > 1 THEN
	        PushLit(par1^.exprType^.targetType^.size);
		Mul(none);
	      END;				(* -|,dst,src,siz	*)
	      CopyBlock(par1^.exprType^.targetType^.alignMask);
	   (* case 3: STR + Elem *)
	    ELSIF NeedsCopy(par2^.exprType^.tyClass,par2^.exprType^.size) THEN
	      MakeObjAndPushAdr(par2);		(* -|,dst,src		*)
	      PushLit(par1^.exprType^.targetType^.size);
	      CopyBlock(par1^.exprType^.targetType^.alignMask);
	    ELSE
	      PushExprValue(par2);
	      ReverseAssign(BaseObjOf(par1^.exprType^.targetType),NIL,unknownT);
	    END;
	| concatP :
	    IF parsFixed THEN pSiz := 0 ELSE pSiz := 4 * bytesInWord END;
	    PushDesig(par1^.name,dVar,dMod);
	    Deref(word,dVar,dMod);		(* -|,blk		*)
	    AdjustParam(bytesInWord,oP1); 
	    IF  (par2^.exprType^.tyClass = stringTs) THEN
	      PushDesig(par2^.name,dVar,dMod);
	      Deref(word,dVar,dMod);		(* -|,blk		*)
	      AdjustParam(bytesInWord,oP2); 
	      pName := stCatBkt;
	    ELSIF (par2^.exprType^.tyClass = SS) OR
		  (par2^.exprType^.tyClass = arrays) THEN
	      MakeObjAndPushAdr(par2);
	      AdjustParam(bytesInWord,oP2); 
	      IF par2^.exprType^.tyClass = SS THEN
                PushLit(par2^.conValue.strHigh + 1);
              ELSIF par2^.exprType^.isDynamic THEN
		Assert(par2^.exprClass = desigNode);
		PushOpenCount(par2);
	      ELSE
		PushLit(IndexCardinality(par2^.exprType));
	      END;
	      AdjustParam(bytesInWord,oP5);
	      pName := ssCatBkt;
	    ELSE (* S1, chars, subranges of char *)
	      PushExprValue(par2);
	      AdjustParam(bytesInWord,oP2); 
	      pName := chCatBkt;
	    END;
	    GetNext(curs,next); Designator(next^.name);
	    AdjustParam(bytesInWord,oP3); (* alloc *)
	    GetNext(curs,next); Designator(next^.name);
	    AdjustParam(bytesInWord,oP4); (* deall *)
	    CallProc(pName, pSiz, 4);
	| haltP : (* are these macros, syscalls or libc calls ? *)
	    PushLit(0);
            AdjustParam(bytesInWord,oP1); (* new DEC 91 *)
	    Trap(exitTrp,1);
	| abortP :
	    Trap(abortTrp,0);
	| incP, decP :
	    sign := IsSignedType(pType);
	    test := ovfloTests IN par1^.testFlags;
	    mode := addMode[sign,test];
            class := pType^.tyClass;
	    objct := BaseObjOf(pType);
	    PushDesig(par1^.name,dVar,dMod);
	    Duplicate;
	    Deref(objct,dVar,dMod);
	    PushExprValue(par2);
	    IF id = incP THEN Add(mode) ELSE Sub(mode) END;
	    IF rangeTests IN par1^.testFlags THEN 
	      IF sign THEN Test(pType,PointerTo(ints));
	      ELSE Test(pType,PointerTo(cards));  (* dst,src *)
	      END;
	    END;
	    ReverseAssign(objct,dVar,dMod);
	| exclP, inclP :
	    PushDesig(par1^.name,dVar,dMod);
	    IF pType^.size > bytesInWord THEN
	      PushExprValue(par2);
	      IF rangeTests IN par2^.testFlags THEN
		Test(pType^.baseType,par2^.exprType);
	      END;
	      BigSetIncl(id = inclP,stat^.sourceLoc.pos,dVar,dMod);
	    ELSE
	      Duplicate;
	      Deref(word,dVar,dMod);
	      PushExprValue(par2);
	      IF rangeTests IN par2^.testFlags THEN
		Test(pType^.baseType,par2^.exprType);
	      END;
	      IF id = exclP THEN
	        SetExcl;
	      ELSE SetIncl;
	      END;
	      ReverseAssign(word,dVar,dMod);
	    END;
	| addAdrP, subAdrP : Assert(FALSE,"bad incAdr");
	| shiftP, rotateP :
	    PushExprAddress(par1);
	    Duplicate;
	    Deref(word,NIL,unknownT);
	    PushExprValue(par2);
	    IF id = shiftP THEN Shift ELSE Rotate END;
	    ReverseAssign(word,NIL,unknownT);
	| exitP :
	    PushExprValue(par1);
            AdjustParam(bytesInWord,oP1); (* new DEC 91 *)
	    Trap(exitTrp,1);
	| assertP, preconP :
	    IF NOT (assertOff IN modState) AND
		((par1^.exprClass <> literalNode) OR
		 (par1^.conValue.fixValue = ORD(FALSE))) THEN
	      AllocateLabel(xLab);
	      IF expandTests OR 
		  ((par2 <> NIL) AND 
		   (par2^.actualX^.exprClass <> literalNode)) THEN
	        BoolJump(par1,fallThrough,xLab);
		IF par2 <> NIL THEN
		  MakeObjAndPushAdr(par2^.actualX);
	  	  PushLit(0);
                  AdjustParam(bytesInWord,oP2); (* new DEC 91 *)
	        ELSE
                  PushModName; 
                  PushLit(stmnt^.sourceLoc.line);
                  AdjustParam(bytesInWord,oP2); (* new DEC 91 *)
		END;
                AdjustParam(bytesInWord,oP1); (* new DEC 91 *)
	        Trap(m2_assTrp,2);
	        CodeLabel(xLab);
	      ELSE 		(* out of line tests ... *)
		IF par2 = NIL THEN
		  IF id = preconP THEN
		    pName := m2_preTrp;
		  ELSE
		    pName := m2_assTrp;
		  END;
		  EmitAssertTest(xLab,pName,0,stmnt^.sourceLoc.line);
		ELSE 
		  EmitAssertTest(xLab,m2_assTrp,par2^.actualX^.rtOffset,0);
		END;
		BoolJump(par1,xLab,fallThrough);
	      END;
	    END;
	END;
      END CallStandardProc;

      VAR typ  : TypeDesc;
	  pNum : CARDINAL;

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
	(*
	 *  for the portable version, the designator
	 *  is pushed last, after the parameters
	 *)
        IF variable^.idClass = varNode THEN (* proc var ... *)
	  typ := TypeOfDes(stat^.designator);
	ELSE typ := variable^.procType;
        END;
        DoParams(typ,seq,parBytes);
	pNum := LengthOf(seq);
        IF variable^.idClass = varNode THEN 
          DerefDesig(stat^.designator,word);
          CallTOSProc(parBytes,pNum);
	ELSE CallProc(variable^.linkName,parBytes,pNum);
	END;
      END;
    END;
    END WriteProcCall;

    PROCEDURE BigSetAssign(exp : ExprDesc);
      VAR size : CARDINAL;
      (* pre  : destination address is top of stack *)
      (* post : stack is popped by one ...	    *)
    BEGIN
      size := exp^.exprType^.size DIV bytesInWord;
      IF exp^.exprClass IN setBinops THEN
	(*
	 *  Binops :
	 *
	 *  first the params are pushed on the stack
	 *  (in reverse order) then the RTSproc is called
	 *)
	BuildBigSet(exp^.leftOp,size);
	BuildBigSet(exp^.rightOp,size);
        PushLit(size);
        AdjustParam(bytesInWord,oP4); (* new DEC 91 *)
	PushExprAddress(exp^.rightOp);
        AdjustParam(bytesInWord,oP3); (* new DEC 91 *)
	PushExprAddress(exp^.leftOp);
        AdjustParam(bytesInWord,oP2); (* new DEC 91 *)
	(*
	 *   destination is top of stack again...
	 * 	this doesn't work with interpreters
	 *)
        AdjustParam(bytesInWord,oP1); (* new DEC 91 *)
      END;
      CASE exp^.exprClass OF
      | plusNode  : RTSproc(cup3,4);
      | slashNode : RTSproc(xor3,4);
      | starNode  : RTSproc(cap3,4);
      | minusNode : RTSproc(dif3,4);
      | preconNode :
	  StatementSeq(exp^.evalLst,0);
	  BigSetAssign(exp^.theCall);
      | setDesigNode, literalNode, desigNode, funcDesigNode, castNode :
	  MakeObjAndPushAdr(exp);
          PushLit(size * bytesInWord);
	  CopyBlock(alignMap[bytesInWord]);
      END;
    END BigSetAssign;

    PROCEDURE RetBoolExpr(fOrT : BOOLEAN; expr : ExprDesc);
      VAR newL : LabelType;
	  invB : BOOLEAN;
    BEGIN
      invB := NOT fOrT;
      CASE expr^.exprClass OF
      | notNode :
	  RetBoolExpr(invB, expr^.notOp);
      | orNode  : 
	  AllocateLabel(newL);
	  BoolJump(expr^.leftOp,newL,fallThrough);
	  PushLit(ORD(fOrT)); 
	  MakeRetValue(byteCard); GenerateReturn();
	  CodeLabel(newL);
	  RetBoolExpr(fOrT,expr^.rightOp);
      | andNode : 
	  AllocateLabel(newL);
	  BoolJump(expr^.leftOp,fallThrough,newL);
	  PushLit(ORD(invB)); 
	  MakeRetValue(byteCard); GenerateReturn();
	  CodeLabel(newL);
	  RetBoolExpr(fOrT,expr^.rightOp);
      ELSE
	  PushExprValue(expr); (* bound to be Boolean *)
	  IF invB THEN NegateBool END;
      END;
    END RetBoolExpr;

  BEGIN (* body of StatementSeq *)
    InitCursor(seq,cursor);
    WHILE NOT Ended(cursor) DO
      GetNext(cursor,stmnt);
      WITH stmnt^ DO
	IF statClass <> emptyNode THEN
	  LineNum(sourceLoc.line);
	END;
        CASE statClass OF
	| compoundNode : StatementSeq(inlineBody,lab);
	| emptyNode    : (* nothing *)
        | ifNode       : IF cseElim IN modState THEN 
			   NewEncodeIf(stmnt); 
			 ELSE OldEncodeIf(stmnt);
			 END;
        | forNode      : EncodeFor(stmnt);
        | caseNode     : EncodeCase(stmnt);
        | exitNode     : Branch(lab);
        | procCallNode : WriteProcCall(stmnt);
        | assignNode :  
            class := expression^.exprType^.tyClass;
	    IF class = sets THEN
	      IF expression^.exprType^.size = bytesInWord THEN (* word set *)
	        PushExprValue(expression);
	        AssignDesig(designator,word);
	      ELSE 
	        Designator(designator);
                BigSetAssign(expression);	(* pops the desig *)
	      END;
	    ELSIF class = RR THEN
	      object := table[desigType^.tyClass];
	      IF expression^.rtOffset = literalZero THEN
	        PushLit(0);  				     (* jl Jun 94 *)
		IF object = double THEN ItoD ELSE ItoF END;
	      ELSIF object = double THEN
		PushCon(expression^.rtOffset);
		Deref(double,NIL,invariant);
	      ELSE (* shorten literal at compile time *)
		PushCon(expression^.rtOffset + bytesInReal); (* jl Jun 94 *)
		Deref(float,NIL,invariant);
	      END;
	      AssignDesig(designator,object);
            ELSIF NOT (class IN specials) THEN  (* sets elsewhere *)
	      object := BaseObjOf(desigType);
	      IF object = hugeInt THEN
	        PushLongValue(expression);
	      ELSE
	        PushExprValue(expression);
	        IF rangeTests IN expression^.testFlags THEN 
	  	  Test(desigType,expression^.exprType); (* dst,src *)
	        END;
	      END;
	      AssignDesig(designator,object);
	    ELSIF class = SS THEN
	      length := desigType^.size;
              Designator(designator);
              PushExprAddress(expression);
	      IF length > expression^.conValue.strHigh THEN
		PushLit(expression^.conValue.strHigh + 1);
	      ELSE PushLit(length);
	      END;
	      CopyBlock(alignMap[1]);			(* pops all three *)
	    ELSE (* arrays and records *)
	      align := expression^.exprType^.alignMask;
	      Designator(designator);
              MakeObjAndPushAdr(expression);
              PushLit(expression^.exprType^.size);
	      CopyBlock(align);			(* pops the desig *)
	    END;
        | loopNode     :
	    AllocateLabel(lLab);
	    AllocateLabel(xLab);
	    LoopLabel(lLab);
	    StatementSeq(loopBody,xLab);
	    Branch(lLab);		    (* loop here *)
	    LoopEnd(lLab);
	    CodeLabel(xLab);		    (* exit here *)
        | returnNode   :
	    IF inExcept THEN FreeDescriptor(exceptDesc) END;
	    IF returnResult <> NIL THEN
(* ================================================= *
 * gp2d returns doubles directly
 *
 *	      IF class = doubles THEN (* copy to dest *)
 *	        (* assert: destination is a local *)
 *		PushDestAdr(); (* either stack or reg *)
 *	        Duplicate;
 *		PushExprValue(returnResult);
 *		ReverseAssign(double);
 * ================================================= *)
	      class := returnResult^.exprType^.tyClass;
	      IF NeedsCopy(class,destTypeDesc^.size) THEN
		(*
		 *  result could be in local ==> copy to dst
		 *)
	        PushDstPointer(class = records);
		IF (returnResult^.exprClass = funcDesigNode) AND
		   (returnResult^.name.variable^.idClass <> stFunc) THEN
		  (*
		   *   Here is one case where the assign must be done
		   *   even in the case that the "function" is a cast, so
		   *   we must step around AssignFunc's castP semantics 
		   *)
		  AssignFuncResult(returnResult,FALSE); (* with no pop *)
	        ELSIF returnResult^.exprClass = constructorNode THEN
		  ConstructSeq(returnResult);	        (* with no pop *)
	        ELSIF returnResult^.exprClass = setDesigNode THEN
		  BigSetConstructor(returnResult,destTypeDesc^.size,FALSE);
		ELSIF returnResult^.exprClass IN setBinops THEN
		  Duplicate;		      (* Next line always pops *)
		  BigSetAssign(returnResult);
	        ELSE	    (* construct if necessary, then copy block *)
		  Duplicate;	(* dst, dst *)
		  (*  need a Make... in case it it is a castP *)
		  MakeObjAndPushAdr(returnResult);	 (* dst, dst,  *)
		  IF class = SS THEN		(* all new sep-92 *)
		    length := destTypeDesc^.size;
		    IF length > returnResult^.conValue.strHigh THEN
		      length := returnResult^.conValue.strHigh + 1;
		    END;
	            PushLit(length);
		  ELSE
		    PushLit(destTypeDesc^.size);   (* new sep-92 *)
	          END;
	          CopyBlock(returnResult^.exprType^.alignMask);
		END;
	      ELSIF (class = RR) AND			(* Nov-92 kjg *)
			(destTypeDesc = PointerTo(floats)) THEN
	       (* shorten literal at compile time *)
		PushFloatConst(returnResult);		(* jl Jun 94 *)
	      ELSIF class = bools THEN
		RetBoolExpr(TRUE,returnResult);
	      ELSE (* NOT special + small sets *)
	        PushExprValue(returnResult);
	        IF rangeTests IN returnResult^.testFlags THEN 
		  Test(destTypeDesc,returnResult^.exprType); (* dst,src *)
	        END;
	      END;
              MakeRetValue(BaseObjOf(destTypeDesc));
            END;
	    IF returnLab = 0 THEN GenerateReturn() ELSE Branch(returnLab) END;
	| retryNode :
	    Assert(inExcept);  (* and retryLab has been allocated *)
	    FreeDescriptor(exceptDesc);
	    Branch(retryLab);
        | tailRecNode  :  ;
        | whileNode    :  
	    AllocateLabel(lLab);
	    AllocateLabel(xLab);
	    BoolJump(condition,xLab,fallThrough);
	    (*
	     * loop header, invariant code goes here
	     *)
	    LoopLabel(lLab);
	    StatementSeq(wrBody,lab);
	    BoolJump(condition,fallThrough,lLab);
	    LoopEnd(lLab);
	    CodeLabel(xLab);
        | repeatNode   :   
	    AllocateLabel(lLab);
	    (*
	     * loop header, invariant code goes here
	     *)
	    LoopLabel(lLab);
	    StatementSeq(wrBody,lab);
	    BoolJump(condition,lLab,fallThrough);
	    LoopEnd(lLab);
        | withNode     :    
            WITH withInfo^ DO
              IF desig.variable <> dummy THEN
		Designator(desig);
		(*
		 *  this places the address of the designator
		 *  on the top of stack. It is always a mem-temp
		 *)
	        MakeWith(dummy,sourceLoc.pos);
              END;
              StatementSeq(withBody,lab);
            END;
        END; (* of case *)
      END; (* with stmnt^ *)
    END;
  END StatementSeq;


  PROCEDURE EmitBlock(idd : IdDesc);
    VAR labS      : LabString;
	exceptLab : LabelType;
	index     : INTEGER;
  BEGIN
    NEW(labS,6);(* list of label triples of the form:
		 *  retryLab  - RETRY branches here
		 *  returnLab - end of protected region
		 *  exceptLab - beginning of handler
		 *)
    WITH idd^ DO
      inExcept := FALSE;
      GenerateEntry(idd);
     (*
      * emit the nested module bodies
      *)
      EmitMods(body^.nestBlks,labS);

      IF hasExcept IN body^.callAttrib THEN
        AllocateLabel(retryLab);
        AllocateLabel(returnLab);
        AllocateLabel(exceptLab);
        APPEND(labS,retryLab);
        APPEND(labS,returnLab);
        APPEND(labS,exceptLab);
        CodeLabel(retryLab);
      END;
     (*
      * emit the code body
      *)
      returnLab := 0;	(* RETURN = exit *)
      StatementSeq(body^.statements,0);

      LineNum(body^.endIdLine);
      IF (idClass = procNode) AND (procType^.tyClass = funcTypes) THEN
	Trap(m2_funTrp,0);
      ELSE
        GenerateReturn();
      END;

     (*
      * emit the exception handlers
      *)
      index := 0;
      inExcept := TRUE;
      exceptDesc := body^.exceptDesc;
      IF hasExcept IN body^.callAttrib THEN
        CodeLabel(labS[HIGH(labS)-1]);  (* end of protected code *)
        EmitModExcepts(body^.nestBlks,labS,index);
(**)    Assert(index = HIGH(labS) - 2);
        CodeLabel(labS[index+2]);       (* the handler label *)
        retryLab  := labS[index];       (* where RETRY goes  *)
        returnLab := 0;		        (* RETURN = exit *)
        StatementSeq(body^.exceptSeq,0);
	PropagateException(idd,exceptDesc);
      ELSIF exceptDesc <> NIL THEN	(* nested module has except *)
        EmitModExcepts(body^.nestBlks,labS,index);
      END;
      GenerateExit(idd,labS);
    END;
    DISPOSE(labS);
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
	EmitProcs(body^.nestBlks); (* recurse down past modNodes *)
	IF idClass <> modNode THEN
	  EmitBlock(idd);	   (* now do the procedure body  *)
	END;
      END;
    END;
  END EmitProcs;

 (* =========================================================== *
  * This procedure recurses over the "nestBlks" strings. This
  * version emits modules, stopping when it gets to a procedure.
  * This version does: most nested first, left-to-right order.
  * =========================================================== *)
  PROCEDURE EmitMods(str : IdString; labS : LabString);
    VAR idx : INTEGER;
	idd : IdDesc;
	exceptLab : LabelType;
  BEGIN
    FOR idx := 0 TO HIGH(str) DO
      idd := str[idx];
      WITH idd^ DO
	IF idClass = modNode THEN 
	  EmitMods(body^.nestBlks,labS);
	(*
	 *DiagName(idd^.outside^.name); StdError.WriteString(" has nestmod: ");
	 *DiagName(idd^.name); StdError.WriteLn;
	 *)

	  AllocateLabel(returnLab);
	  IF hasExcept IN body^.callAttrib THEN
	    AllocateLabel(retryLab);
	    AllocateLabel(exceptLab);
	    APPEND(labS,retryLab);
	    APPEND(labS,returnLab);
	    APPEND(labS,exceptLab);
	    CodeLabel(retryLab);	(* RETRYs will jump back to here *)
	  END;
	 (*
	  * emit the module body
	  *)
	  StatementSeq(body^.statements,0);
	  CodeLabel(returnLab);		(* RETURNs will jump forward to here *)
	END;
      END;
    END;
  END EmitMods;

 (* =========================================================== *
  * This procedure recurses over the "nestBlks" strings.
  * This version emits module body exception handlers.
  * =========================================================== *)
  PROCEDURE EmitModExcepts(str : IdString; labS : LabString; VAR index : INTEGER);
    VAR idx : INTEGER;
	idd : IdDesc;
  BEGIN
    FOR idx := 0 TO HIGH(str) DO
      idd := str[idx];
      WITH idd^ DO
	IF idClass = modNode THEN 
	  EmitModExcepts(body^.nestBlks,labS,index);
	 (*
	  * emit the exception handlers
	  * the order of code emmission is in principle unimportant
	  * except that we must match the labels to the correct body
	  * so the traversal here must mirror EmitMods exactly
	  *)
	  IF hasExcept IN body^.callAttrib THEN
	    CodeLabel(labS[index+2]);
	    returnLab := labS[index+1];
	    retryLab  := labS[index];
	    StatementSeq(body^.exceptSeq,0);
	    PropagateException(idd,exceptDesc);
	    INC(index,3);
	  END;
	END;
      END;
    END;
  END EmitModExcepts;

  PROCEDURE EmitOutput;
    VAR cursor : ElemPtr;
        idPtr  : IdDesc;
  BEGIN
    charPtr := PointerTo(chars);
    CreateObjFile(thisCompileUnit^.name);
    (*
     *  create a dummy designator for 
     *  function destination addresses.
     *  Via-C versions do not need this (kjg Sep-92)
     *)
    InitTable; (* set up m2rts names *)
    EnterString("__HMIN__",hMinBkt);
    EnterString("__HMAX__",hMaxBkt);
    EnterString("__XPNDSTR__",xpndBkt);
    EnterString("__CHCATST__",chCatBkt);
    EnterString("__SSCATST__",ssCatBkt);
    EnterString("__STCATST__",stCatBkt);
    (*
     *  emit the header comment
     *  and then the declarations
     *  including imports
     *)
    DoObjHeader(thisCompileUnit^.name);
    EmitProcs(thisCompileUnit^.body^.nestBlks);
    WriteWrappers();
    EmitBlock(thisCompileUnit);
    (*
     *  here the used list of RTS calls must be emitted
     *)
    DoObjEnd;
    CloseObjFile();
    WriteRefFile(callSmbl);
  END EmitOutput;

END M2ObjectCode.
