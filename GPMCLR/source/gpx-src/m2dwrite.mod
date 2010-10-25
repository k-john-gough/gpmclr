(****************************************************************)
(*                                                              *)
(*              Modula-2 Compiler Source Module                 *)
(*                                                              *)
(*         Code Generation and D-Code Assembly Output           *)
(*                                                              *)
(*     (c) copyright 1990 Faculty of Information Technology     *)
(*                                                              *)
(*      original module : kjg January 1990                      *)
(*      modifications   : D-Code modifications kjg    10-Aug-90 *)
(*                      : changed pshFP, pshDsp kjg   28-Dec-90 *)
(*                      : dwc Jan/Feb 91                        *)
(*                      :   SetRelop, CardRelop, IntRelop,      *)
(*                      :    BigSetRelop changed to allow for   *)
(*                      :    new D-codes                        *)
(*                      :   GenerateExit - no exit produced     *)
(*                      :    for functions                      *) 
(*                      :   MakeRetValue - parameter deleted    *)
(*                      :   GenerateReturn added                *)
(*                      :   Code for StrLength added            *)
(*                      :   LastInstruction added               *)
(*                      :   Object Code output                  *)
(*                      : dwc 5-Mar-91                          *)
(*                      :   BackPatching added                  *)
(*                      : jrh 06-Jun-91 SplitRecord restructured*)
(*			: kjg 20-jun-91 float ops incorporated  *)
(*			: kjg  3-aug-91 peephole optimization	*)
(*								*)
(* new version editted from the file "M2CodeGenerator" 2-Sep-91 *)
(*								*)
(*   =============== merged mips and i386 source ============	*)
(*			   kjg 22 Mar 93			*)
(*      modifications   : 					*)
(*								*)
(**************************************************************** 
$Log: m2dwrite.mod,v $
Revision 1.29  1997/01/16 02:59:42  gough
delete use of currName.
Link-names are added to IdDescs, rather than overwriting the name field.
Hence PushAdr etc are changed.  EmitAssertTest also takes a name param.

Revision 1.28  1996/11/27 01:57:51  lederman
add FreeDescriptor() & PropagateException() and modify GenerateExit() to emit
the except table and if exceptOK flag is set the default propagation entry

Revision 1.27  1996/05/10 06:57:56  lederman
change all procedures that take param. offset to use INTEGER

Revision 1.26  1996/01/08 05:27:13  gough
Deref, Assign etc have extra attributes for alias markers

Revision 1.25  1995/10/18 00:41:06  lederman
generate correctly signed SHORTREAL infinity

Revision 1.24  1995/10/10 23:18:50  lederman
DCode V3 HugeInt support stuff

Revision 1.23  1995/09/15 07:41:38  gough
new code for PushBool --- not using the deprecated pshFi, popFi

# Revision 1.22  1995/05/02  01:54:12  lederman
# Don't try to SFLOAT(HUGE) as this doesn't work on Alpha
#
# Revision 1.21  1995/05/01  22:43:19  gough
# at the end of CopyArrays, formal parameters are warped to varForm,
# but only if they are ref params _and_ are not open arrays. This fixes
# a bug with open arrays of array element types not getting a $hi value.
#
# Revision 1.20  1995/03/23  22:55:46  gough
# code to deal with multidimensional open arrays for EXPAND
#
# Revision 1.19  1995/03/17  02:55:24  lederman
# fix dumping string literals to ignore 0C and just dump to strHigh
#
# Revision 1.18  1995/03/14  01:12:19  gough
# Code for marshalling of open array parameters on the caller side
# Also auto class variables in the global scope go to the stack frame,
# there are corresponding changes in m2procstate and m2objectcode
#
# Revision 1.17  1995/02/23  03:51:06  lederman
# for Alpha: if SHORTREAL literal overflows dump +infinity
# also add gdb-info to destination of CopyParams
#
# Revision 1.16  1995/01/06  03:36:04  gough
# remove .ENDCASE, replace by comment
#
# Revision 1.15  1995/01/05  05:39:24  gough
# Include new interface proc Switch(lab : LabelType) for CASE statements
#
# Revision 1.14  1994/12/01  00:25:00  lederman
# emit endId line number in GenerateExit
#
# Revision 1.13  1994/11/15  04:27:37  gough
# put in gdb support
#
# Revision 1.12  1994/10/12  23:29:56  lederman
# fix typo
#
# Revision 1.11  1994/10/12  05:57:01  lederman
# handle -ve param bytes for retCut with parsFixed
#
# Revision 1.10  1994/10/12  04:44:17  gough
# new procedure RngAssert
#
# Revision 1.9  1994/10/11  07:16:22  gough
# separate concept of IsRefParam and IsCopyParam
#
# Revision 1.8  1994/10/10  05:13:01  gough
# changes for writing out value mode records with sunStructs flag
#
# Revision 1.7  1994/08/22  05:04:07  gough
# local fps now use "fpParam" and import/export vars give size
#
# Revision 1.6  1994/07/15  03:12:43  lederman
# assignW => assignF
#
# Revision 1.5  1994/07/13  23:18:39  gough
# fix declaration of pointers to value array params as .LOCALs
#
# Revision 1.4  1994/07/01  04:30:09  lederman
# update D-Code strings; removed all 32-bit dependancies
# .SHORT => .BITS16; .WORD => .BITS32 for 64-bit targets
#
# Revision 1.3  1994/06/20  06:44:57  gough
# output explicit local declaration for refs to value fixed arrays
#
# Revision 1.2  1994/06/07  07:04:28  gough
# new procedure NegateBool
#
# Revision 1.1  1994/04/21  06:33:12  lederman
# Initial revision
#
*****************************************************************
Revision 1.21  94/02/22  12:23:16  gough
fix up names of uToDbl and uToFlt (oops)

Revision 1.20  94/02/17  08:29:48  gough
fix up entier, round, rotate, etc. and place mode markers on abs,
negate, and the real --> whole number conversions.

Revision 1.19  94/02/07  09:23:30  gough
put in extra dereference for optimized array parameter PushAdrs

Revision 1.18  94/02/01  16:09:58  gough
fix up coercion of character consts in SpillElem

Revision 1.17  93/11/17  11:40:16  gough
don't put out RETCUT on module bodies ...

Revision 1.16  93/11/16  08:49:27  gough
emit the ".RETCUT=nnn" for procedure where necessary

Revision 1.15  93/10/08  13:55:53  gough
make AllocateFi and Push/PopFi visible to M2ObjectCode

Revision 1.14  93/10/04  17:06:24  gough
output import statement for gpMrts functions as needed by pc and nt vers.

Revision 1.13  93/09/30  10:30:15  gough
output the header line as the first line of dcode

Revision 1.12  93/09/10  17:48:34  gough
change WriteLocal so that high values have their own .LOCAL declaration

Revision 1.11  93/08/06  08:32:45  gough
don't forget to send param count for calls to _strLen

Revision 1.10  93/08/05  17:42:57  gough
implement param numbers for calls and traps

Revision 1.9  93/07/01  08:20:18  mboss
fix attribute evaluation for local information

Revision 1.8  93/06/30  16:24:16  mboss
remove uses of isExternal

Revision 1.7  93/06/08  08:41:09  mboss
fix counting of fi-ordinals in PushBool() ... (kjg)

Revision 1.6  93/06/07  17:11:11  mboss
installing log in file (kjg)
*****************************************************************)
 

IMPLEMENTATION MODULE M2DWriter;

  IMPORT Ascii, StdError, SYSTEM, Storage;

  FROM ProgArgs IMPORT Assert, FP_Overflow;

  FROM Types IMPORT Card8, Card16, Card32;

  FROM GenSequenceSupport IMPORT 
        Sequence, LinkLeft, LinkRight, InitSequence, InitCursor,
        IsEmpty, Ended, DisposeList, ElemPtr, GetNext, NextIsLast;

  FROM M2ProcState IMPORT 
        StatLinkAttributes, LexLevel,
        SetCurrentEnv, tmpOffset, IsCopyParam, IsRefParam,
        copyOffset, isMain;

  FROM M2NodeDefs IMPORT
	UsesSet, VarUses,
        modState, FormalType, FormalClass, IdDesc, StrucTree,
        Attribute, AttributeSet, TypeDesc, 
        IdTree, TyNodeClass, TyClassSet, IdNodeClass, thisCompileUnit;

  FROM M2DDefinitions IMPORT
        Instruction, Object, LabelType, TempIndex, Relops, ModeEnum;

  FROM M2LitChain IMPORT
        chainHead, chainTail, ConstDataSize;

  FROM M2Designators IMPORT 
	AccessMode, ExprDesc, ExprRec, ExprNodeClass, ExpandInfo;

  FROM M2Alphabets IMPORT 
	LexAttType, HashBucketType, ModStateFlags, ModStateSet, ConBlock;

  FROM M2InOut IMPORT 
	DiagName, WriteObjByte, 
	EmitFileName, lastPos, ErrIdent, debugOn;

  FROM M2NameHandler IMPORT 
	anonBkt, EnterString, StringTable, GetSourceRep;

  FROM M2MachineConstants IMPORT 
	stackMarkSize, bytesInWord, adrSize, extRecRetPtr, 
	extArrRetPtr, parsFixed, bytesInReal, bigEndian, 
	crossEndian, destOffset, gdbSupport, exceptOK, INFINITY;

  FROM M2SSUtilities IMPORT LookupInThisScope, Align;
  FROM M2NamGenerate IMPORT callSmbl;
  FROM M2RTSInterface IMPORT equ, neq, geq, leq, strLen;
  FROM M2GdbSupport  IMPORT EmitInitialTypes,EmitObject,EmitTypeDef,EmitLocal;
  FROM M2TabInitialize IMPORT PointerTo;

(*====================================================*)

  CONST conDataStr = "__cDat";
	modNameStr = "__mNam";

  TYPE  StringType = ARRAY [0 .. 127] OF CHAR;

  TYPE  ModeMap    = ARRAY ModeEnum OF ARRAY [0 .. 7] OF CHAR;
  TYPE  FormSet    = SET OF FormalClass;

  CONST intOverS = "intOver";
  CONST crdOverS = "crdOver";
  CONST noTrapS  = "noTrap";

  CONST modeStr  = ModeMap{"", intOverS, crdOverS};

  VAR   thisName : StringType;
	jumpSeq  : Sequence;
	withTmp  : HashBucketType;
	hiType   : TypeDesc;
	aliasInf : BOOLEAN;

(*====================================================*)

(*====================================================*)

    TYPE RelopTable = ARRAY [0..5] OF Instruction;
    TYPE InstructionTable = ARRAY Object OF Instruction;

    CONST realClasses  = TyClassSet{RR,floats,doubles};
    	  strucClasses = TyClassSet{records,arrays};

  PROCEDURE InitCodeGen(hsh : HashBucketType); FORWARD;

(*====================================================*)
  MODULE WriteDASM;

    IMPORT 
        WriteObjByte, Card8, Relops,
	Ascii, Instruction, GetSourceRep,
	thisName, EmitFileName, 
	StringType, HashBucketType;

    EXPORT 
	BuffI, BuffRelEol, BuffS, BuffN, 
	BuffInt, BuffCrd, BuffEol, 
	Space, Comma, WriteByte, 
	WriteEndRecord, WriteHeaderRecord;

(* ==================================================== *)
(*  Implementation  automatically produced by MkEnumIO  *)
(* ==================================================== *)

  CONST tMx = 989;

  TYPE Index = ARRAY Instruction OF CARDINAL;
       StTab = ARRAY [0 .. tMx] OF CHAR;

  CONST enumStart = Index{
	0, 6, 14, 19, 24, 32, 39, 46, 53, 59, 
	66, 74, 80, 87, 92, 99, 106, 112, 119, 127, 
	135, 144, 153, 162, 171, 178, 185, 192, 199, 207, 
	216, 225, 233, 241, 249, 257, 264, 269, 276, 284, 
	288, 293, 299, 303, 308, 312, 317, 321, 326, 330, 
	335, 339, 344, 348, 353, 359, 366, 373, 380, 389, 
	398, 405, 411, 418, 425, 432, 439, 447, 453, 459, 
	465, 471, 477, 485, 493, 499, 505, 511, 517, 523, 
	529, 535, 541, 549, 556, 561, 566, 571, 580, 589, 
	599, 609, 619, 629, 637, 645, 653, 661, 669, 677, 
	685, 693, 701, 708, 715, 722, 729, 736, 743, 750, 
	757, 764, 771, 778, 785, 792, 799, 806, 813, 820, 
	827, 834, 841, 848, 855, 862, 869, 876, 883, 890, 
	897, 904, 911, 919, 927, 935, 941, 947, 955, 963, 
	968, 973, 980, 985
    }; (* compile errors here mean that type 'Instruction'
	* has changed its cardinality since module 'InstructionIO'
	* was created. Rerun MkEnumIO to fix this module	*)

  CONST stringTab = StTab{
	"e","r","r","o","r","",
	"l","i","n","e","N","u","m","",
	"p","o","p","1","",
	"d","u","p","1","",
	"c","u","t","P","a","r","s","",
	"a","d","d","O","f","f","",
	"a","d","d","A","d","r","",
	"b","l","k","P","a","r","",
	"m","k","P","a","r","",
	"m","k","D","s","t","P","",
	"p","s","h","D","s","t","P","",
	"m","k","T","m","p","",
	"p","s","h","T","m","p","",
	"p","s","h","Z","",
	"p","s","h","L","i","t","",
	"p","s","h","A","d","r","",
	"p","s","h","F","P","",
	"p","s","h","D","s","p","",
	"d","e","r","e","f","U","B","",
	"d","e","r","e","f","S","B","",
	"d","e","r","e","f","U","1","6","",
	"d","e","r","e","f","S","1","6","",
	"d","e","r","e","f","U","3","2","",
	"d","e","r","e","f","S","3","2","",
	"d","e","r","e","f","W","",
	"d","e","r","e","f","L","",
	"d","e","r","e","f","F","",
	"d","e","r","e","f","D","",
	"a","s","s","i","g","n","B","",
	"a","s","s","i","g","n","1","6","",
	"a","s","s","i","g","n","3","2","",
	"a","s","s","i","g","n","W","",
	"a","s","s","i","g","n","L","",
	"a","s","s","i","g","n","F","",
	"a","s","s","i","g","n","D","",
	"n","e","g","a","t","e","",
	"n","e","g","L","",
	"b","i","t","N","e","g","",
	"b","o","o","l","N","e","g","",
	"a","b","s","",
	"a","b","s","L","",
	"b","l","k","C","p","",
	"a","d","d","",
	"a","d","d","L","",
	"s","u","b","",
	"s","u","b","L","",
	"m","u","l","",
	"m","u","l","L","",
	"m","o","d","",
	"m","o","d","L","",
	"d","i","v","",
	"d","i","v","L","",
	"r","e","m","",
	"r","e","m","L","",
	"s","l","a","s","h","",
	"s","l","a","s","h","L","",
	"s","h","i","f","t","V","",
	"s","h","L","e","f","t","",
	"s","h","R","i","g","h","t","U","",
	"s","h","R","i","g","h","t","S","",
	"r","o","t","a","t","e","",
	"o","r","W","r","d","",
	"a","n","d","W","r","d","",
	"x","o","r","W","r","d","",
	"b","r","a","n","c","h","",
	"b","r","T","r","u","e","",
	"b","r","F","a","l","s","e","",
	"r","e","l","E","Q","",
	"r","e","l","N","E","",
	"s","e","t","I","n","",
	"s","e","t","L","E","",
	"s","e","t","G","E","",
	"s","e","t","I","n","c","l","",
	"s","e","t","E","x","c","l","",
	"c","r","d","L","S","",
	"c","r","d","L","E","",
	"c","r","d","G","T","",
	"c","r","d","G","E","",
	"i","n","t","L","S","",
	"i","n","t","L","E","",
	"i","n","t","G","T","",
	"i","n","t","G","E","",
	"p","o","p","C","a","l","l","",
	"s","w","i","t","c","h","",
	"e","x","i","t","",
	"t","r","a","p","",
	"c","a","l","l","",
	"p","s","h","R","e","t","U","B","",
	"p","s","h","R","e","t","S","B","",
	"p","s","h","R","e","t","U","1","6","",
	"p","s","h","R","e","t","S","1","6","",
	"p","s","h","R","e","t","U","3","2","",
	"p","s","h","R","e","t","S","3","2","",
	"p","s","h","R","e","t","W","",
	"p","s","h","R","e","t","L","",
	"p","s","h","R","e","t","F","",
	"p","s","h","R","e","t","D","",
	"p","o","p","R","e","t","W","",
	"p","o","p","R","e","t","L","",
	"p","o","p","R","e","t","F","",
	"p","o","p","R","e","t","D","",
	"l","o","n","g","R","e","l","",
	"u","T","o","S","6","4","",
	"i","T","o","S","6","4","",
	"l","T","o","W","r","d","",
	"a","b","s","F","l","t","",
	"a","b","s","D","b","l","",
	"a","d","d","F","l","t","",
	"s","u","b","F","l","t","",
	"m","u","l","F","l","t","",
	"d","i","v","F","l","t","",
	"a","d","d","D","b","l","",
	"s","u","b","D","b","l","",
	"m","u","l","D","b","l","",
	"d","i","v","D","b","l","",
	"u","T","o","F","l","t","",
	"u","T","o","D","b","l","",
	"i","T","o","F","l","t","",
	"i","T","o","D","b","l","",
	"f","T","o","D","b","l","",
	"d","T","o","F","l","t","",
	"f","l","t","R","e","l","",
	"d","b","l","R","e","l","",
	"f","T","r","u","n","c","",
	"d","T","r","u","n","c","",
	"f","R","o","u","n","d","",
	"d","R","o","u","n","d","",
	"f","F","l","o","o","r","",
	"d","F","l","o","o","r","",
	"n","e","g","F","l","t","",
	"n","e","g","D","b","l","",
	"l","T","o","D","b","l","",
	"d","T","r","u","n","c","L","",
	"d","F","l","o","o","r","L","",
	"d","R","o","u","n","d","L","",
	"p","s","h","F","i","",
	"p","o","p","F","i","",
	"f","l","a","t","t","e","n","",
	"m","a","k","e","A","d","r","",
	"s","w","a","p","",
	"t","e","s","t","",
	"a","s","s","e","r","t","",
	"e","n","d","P","",
	"e","n","d","F",""};

(* ==================================================== *)

    PROCEDURE BuffI(val : Instruction);
      VAR index : CARDINAL;
    BEGIN
      WriteObjByte(Ascii.ht);
      index := enumStart[val];
      WHILE stringTab[index] <> '' DO
        WriteObjByte(stringTab[index]);
        INC(index);
      END;
      WriteObjByte(Ascii.ht);
    END BuffI;

    PROCEDURE WriteByte(b : Card8);
    BEGIN
      WriteObjByte(b);
    END WriteByte;

    PROCEDURE Space();
    BEGIN
      WriteObjByte(" ");
    END Space;

    PROCEDURE Comma();
    BEGIN
      WriteObjByte(",");
    END Comma;

    PROCEDURE BuffEol();
    BEGIN
      (*
       *  This is a version dependency caused by the
       *  fact that M2Inout writes to a binary file
       *  THIS VERSION IS FOR UNIX
       *)
      WriteObjByte(Ascii.lf);
    END BuffEol;

    PROCEDURE BuffRelEol(rel : Relops);
    BEGIN
      CASE rel OF
      | eqR : BuffS(" =");
      | neR : BuffS(" <>");
      | gtR : BuffS(" >");
      | geR : BuffS(" >=");
      | lsR : BuffS(" <");
      | leR : BuffS(" <=");
      END;
      BuffEol();
    END BuffRelEol;
      
    PROCEDURE BuffCrd(c : CARDINAL);
      VAR str : StringType;
	  idx : [0 .. 31];
    BEGIN
      IF c = 0 THEN WriteObjByte('0'); RETURN END;
      idx := 0;
      REPEAT
	str[idx] := CHR(c MOD 10 + ORD('0'));
	c := c DIV 10;
	INC(idx);
      UNTIL c = 0;
      FOR idx := idx - 1 TO 0 BY -1 DO 
        WriteObjByte(str[idx]);
      END;
    END BuffCrd;

    PROCEDURE BuffInt(c : INTEGER);
    BEGIN
(* !!! is this safe for c = minInt  ??? *)
(* !!! only if range checks are off !!! *)
(* $T- *) (* $R- *) (* $I- *)
      IF c < 0 THEN
	WriteObjByte("-");
	c := -c;
      END;
      BuffCrd(c);
(* $I= *) (* $R= *) (* $T= *)
    END BuffInt;

    PROCEDURE BuffN(n : HashBucketType);
      VAR ix,jx : CARDINAL;
          st : StringType;
    BEGIN
      ix := 1;
      st[0] := "_";
      GetSourceRep(n,st,ix);
      FOR jx := 0 TO ix - 1 DO
        WriteObjByte(st[jx]);
      END;
    END BuffN;
      
    PROCEDURE BuffS(s : ARRAY OF CHAR);
      VAR ix : CARDINAL; ch : CHAR;
    BEGIN
      FOR ix := 0 TO HIGH(s) DO
        ch := s[ix];
        IF ch = "" THEN RETURN ELSE WriteObjByte(ch) END;
      END;
    END BuffS;

    PROCEDURE WriteEndRecord;
    BEGIN
    END WriteEndRecord;

    PROCEDURE WriteHeaderRecord();
      CONST title = ".TITLE ";
	    file  = '.FILE ';
	    headr = "; D-Code output produced by gpm from ";
      VAR str : StringType;
          idx : CARDINAL;
    BEGIN
      EmitFileName(headr);
      BuffEol;
      BuffS(title); 
      BuffS(thisName); 
      BuffEol;
      EmitFileName(file);
      BuffEol;
    END WriteHeaderRecord;

  END WriteDASM;
(*====================================================*)
  MODULE LitChainDump;
  IMPORT StdError;
  IMPORT BuffS, BuffEol, Comma , conDataStr, modNameStr, thisName;

  IMPORT LabelType, AllocateLabel, HashBucketType, FP_Overflow,
         chainTail, chainHead, thisCompileUnit, callSmbl,
         ExprDesc, ExprRec, bytesInReal, bytesInWord,
	 IdDesc, TypeDesc, LexAttType, ExprNodeClass, GetSourceRep,
	 EnterString, StrucTree, StringType, bigEndian, crossEndian,
         ConBlock, TyNodeClass, Assert, StringTable, INFINITY, Card32;

  IMPORT InitCursor, ElemPtr, Ended, GetNext, WriteObjByte;

  EXPORT EmitLitChain;

  (*
   *  this code is endian independent of the host machine
   *)

    TYPE  Map = ARRAY [0 .. 15] OF CHAR;
    CONST map = Map{"0","1","2","3","4","5","6","7",
		    "8","9","A","B","C","D","E","F"};

    VAR  num, total  : CARDINAL;
         str : ARRAY [0 .. 3] OF CHAR;
         end : ARRAY [0 .. 9] OF CHAR;

    PROCEDURE SpillAscii;
      VAR ix : CARDINAL;
    BEGIN
      IF num <> 0 THEN
        FOR ix := 1 TO (8 - num) DO BuffS("     ") END;
        end[num] := "]";
        end[num + 1] := "";
	BuffS("   ; ["); BuffS(end);
      END;
    END SpillAscii;

    PROCEDURE Spill(ch : CHAR);
    BEGIN
      IF num = 0 THEN BuffS("	.BYTE ") ELSE Comma END;
      IF (ch >= " ") AND (ch < 177C) THEN end[num] := ch;
      ELSE end[num] := ".";
      END;
      str[1] := map[ORD(ch) DIV 16];
      str[2] := map[ORD(ch) MOD 16];
      BuffS(str);
      INC(num); INC(total);
      IF num = 8 THEN 
	SpillAscii;
	BuffEol; num := 0;
      END;
    END Spill;

    PROCEDURE DumpLitExpr(ptr : ExprDesc);
      TYPE Bytes = ARRAY [0 .. 3] OF CHAR;
      VAR  spix, ix : CARDINAL;
	   index    : CARDINAL;
           ch       : CHAR;
           vPtr     : ConBlock;
	   lTyp     : TypeDesc;
	   lVal     : LexAttType;
	   short    : RECORD CASE : INTEGER OF
			| 0 : flt   : SHORTREAL;
			| 1 : card  : Card32;
			| 2 : bytes : Bytes;
		      END END;
    BEGIN
      IF ptr^.exprClass = selConstNode THEN
	lTyp := ptr^.name.variable^.conType;
	lVal := ptr^.name.variable^.conValue;
      ELSE
	lTyp := ptr^.exprType;
	lVal := ptr^.conValue;
      END;
      IF lTyp^.tyClass = sets THEN
	Assert(total <= ptr^.rtOffset);
	WHILE total < ptr^.rtOffset DO Spill(0C) END;
        spix := lVal.patternIx;
	ix := 0;
        WHILE ix < lTyp^.size DO			(* jl Jun 94 *)
	  (* must emit in target endian style *)
	  IF bigEndian <> crossEndian THEN (* big endian *)
	    FOR index := spix + bytesInWord - 1 TO spix BY -1 DO
	      Spill(StringTable(index));
	    END;
	  ELSE (* little endian *)
	    FOR index := spix TO spix + bytesInWord - 1 DO
	      Spill(StringTable(index));
	    END;
          END;
	  INC(ix,bytesInWord); INC(spix,bytesInWord);
        END;
      ELSIF (lTyp^.tyClass = SS) THEN (* is string *)
 	Assert(total = ptr^.rtOffset);
	IF lVal.stringIx = 0 THEN (* charNum being coerced *);
          (*
           *  changes for charNums 12-Jun-90
           *  needed in order to add string concatenation
           *)
          ch := lVal.charValue;
          Spill(ch); Spill(0C);
	ELSE
	  FOR spix := lVal.stringIx TO lVal.stringIx + lVal.strHigh DO
 	    Spill(StringTable(spix));
	  END;
	END;
      ELSIF (lTyp^.tyClass = RR) THEN (* is real *)
        Assert(total <= ptr^.rtOffset);
        WHILE total < ptr^.rtOffset DO Spill(0C) END;
	FP_Overflow := (lVal.floatValue = INFINITY) OR
		       (lVal.floatValue = -INFINITY);
	IF NOT FP_Overflow THEN short.flt := SFLOAT(lVal.floatValue) END;
	IF FP_Overflow THEN		(* Alpha dumps junk otherwise *)
	  IF lVal.floatValue = -INFINITY THEN	(* if SFLOAT overflows*)
	    short.card := 0FF800000H;		(* jl Jun 94 & Oct 95 *)
	  ELSE
	    short.card := 07F800000H;
	  END;
	END;
	IF crossEndian THEN
	  FOR ix := bytesInReal - 1 TO 0 BY -1 DO
	    Spill(lVal.bytes[ix]);
          END;
	  FOR ix := 3 TO 0 BY -1 DO
	    Spill(short.bytes[ix])
	  END;
	ELSE
          FOR ix := 0 TO bytesInReal - 1 DO
	    Spill(lVal.bytes[ix]);
          END;
	  FOR ix := 0 TO 3 DO
	    Spill(short.bytes[ix])
	  END;
	END;
      ELSE
        Assert(total <= ptr^.rtOffset);
        WHILE total < ptr^.rtOffset DO Spill(0C) END;
	vPtr := lVal.adrsValue;
        FOR ix := 0 TO lTyp^.size - 1 DO
	  Spill(vPtr^[ix]);
        END;
      END;
    END DumpLitExpr; 

(*
 *  PROCEDURE NameSpill (name : HashBucketType);
 *  VAR index, i : CARDINAL;
 *      nam : StringType;
 *  BEGIN
 *    index := 0;
 *    GetSourceRep(name,nam,index);
 *    FOR i := 0 TO index DO
 *      Spill(nam[i]);
 *    END; 
 *  END NameSpill;
 *)

    PROCEDURE EmitLitChain();
      VAR ptr : ExprDesc;
          cursor : ElemPtr;
          idPtr : IdDesc;
    BEGIN
      BuffS(".CONST"); BuffEol;
      BuffS(modNameStr); WriteObjByte(":");
      BuffS('	.ASCIIZ "'); BuffS(thisName); 
      WriteObjByte('"'); BuffEol;

      num := 0; total := 0;
      str := "0xxH";
      BuffS(".CONST"); BuffEol;	(* realign on octo boundary *)
      (* now the literal chain (if not empty) is added *)
      IF chainHead <> NIL THEN
	BuffS(conDataStr); WriteObjByte(':');
        ptr := chainHead;
        LOOP
          DumpLitExpr(ptr);
          IF ptr = chainTail THEN EXIT END;
          ptr := ptr^.chainLnk;
        END;
      END;
      SpillAscii;
      BuffEol;
    END EmitLitChain;

  END LitChainDump;

(*====================================================*)

  PROCEDURE InitNames;
    VAR index : CARDINAL;
  BEGIN
    index := 0;
    GetSourceRep(thisCompileUnit^.name,thisName,index);
    EnterString("$WthTmp$",withTmp);
    hiType := PointerTo(cards);
  END InitNames;
    
  PROCEDURE DoObjHeader(modName : HashBucketType);
  BEGIN
    InitNames;
    InitCodeGen(modName);
    WriteHeaderRecord();
    DoPublicsAndExterns;
    EmitLitChain;
  END DoObjHeader;

  PROCEDURE DoObjEnd;
  BEGIN
    WriteEndRecord;
  END DoObjEnd;

  PROCEDURE DoPublicsAndExterns;

    TYPE  PreType = (ext,pub,loc);

    CONST extPre = ".IMPORT _";
	  pubPre = ".EXPORT _";
	  locPre = ".LOCAL  _";
    
    PROCEDURE AddLinkNm(pre : PreType; 
			hsh : HashBucketType);
      VAR str : StringType;
          idx : CARDINAL;
    BEGIN
      IF pre = ext THEN str := extPre;
      ELSIF pre = loc THEN str := locPre;
      ELSE str := pubPre;
      END;
      idx := LENGTH(extPre);
      GetSourceRep(hsh,str,idx);
      BuffS(str); 
    END AddLinkNm;

    PROCEDURE Defs(tree : IdTree);
    BEGIN
      IF tree <> NIL THEN (* do pre-order walk *)
        WITH tree^.ident^ DO
	  IF  (idClass = varNode) AND
	      (varType^.size > 0) THEN
	    IF varClass = extern THEN 
	      AddLinkNm(ext,linkName);  
	      BuffS(" : "); BuffCrd(varType^.size); BuffEol;
	    ELSIF varClass = export THEN 
	      AddLinkNm(pub,linkName);  
	      BuffS(" : "); BuffCrd(varType^.size); BuffEol;
	    END;
          ELSIF idClass = externProc THEN
            AddLinkNm(ext,linkName);  BuffEol;
	  ELSIF idClass = procHeader THEN
            AddLinkNm(pub,linkName);  BuffEol;
          END;
        END;
        Defs(tree^.left); Defs(tree^.right);
      END;
    END Defs;

    PROCEDURE Variable(scp : IdTree);
      VAR str : StringType;
	  idx : CARDINAL;
          siz : CARDINAL;
    BEGIN
      IF scp <> NIL THEN
        WITH scp^.ident^ DO
	  IF  (idClass = varNode) AND
	      (varClass <> auto) AND 
	      (varClass <> extern) AND 
	      (varType^.size > 0) THEN
	    IF debugOn AND gdbSupport THEN EmitObject(scp^.ident) END;
	    str := '  _'; idx := 3;
	    GetSourceRep(linkName,str,idx);
	    BuffS(str);
	    CASE varType^.alignMask OF
	    | 0C : BuffS(": .BYTE ");
	    | 1C : BuffS(": .BITS16 ");
	    | 3C : IF bytesInWord = 4 THEN
		     BuffS(": .WORD ");
		   ELSE
		     BuffS(": .BITS32 ");
		   END;
	    | 7C : IF bytesInWord = 8 THEN
	    	     BuffS(": .WORD ");
		   ELSE
	    	     BuffS(": .DOUBLE ");
		   END;
	    END;
	    BuffCrd(varType^.size DIV (ORD(varType^.alignMask) + 1)); 
	    BuffEol;
	  END;
	END;
	Variable(scp^.left); Variable(scp^.right);
      END;
    END Variable;

    PROCEDURE WriteRTSImports();
    BEGIN
    BuffS("; functions imported from gpmrts");
    BuffEol;
    BuffS(".IMPORT __clr, __geq, __leq, __equ, __neq, __cap2, __cap3, __cup2");
    BuffEol;
    BuffS(".IMPORT __cup3, __xor2, __xor3, __dif2, __dif3, __strLen");
    BuffEol;
    BuffS(".IMPORT __gp_modTrp, __gp_rTrpLI, __gp_rTrpHU, __setRngIncl");
    BuffEol;
    END WriteRTSImports;

    VAR cursor : ElemPtr;
	idPtr  : IdDesc;
  BEGIN
(*
 *  AddLinkNm(pub,callSmbl); BuffEol; (* not needed since changes to namgen *)
 *)
    Defs(thisCompileUnit^.scope); 
    BuffEol;
    WriteRTSImports();
    BuffEol;
    IF debugOn AND gdbSupport THEN EmitInitialTypes END;
    BuffS(".VAR"); BuffEol;
    Variable(thisCompileUnit^.scope); 
    BuffEol;
  END DoPublicsAndExterns;

(*====================================================*)


  MODULE LabelControl;
    (*
     *  In this version labels are global to module
     *)

    IMPORT 
        LabelType, BuffS, BuffCrd, BuffEol, WriteObjByte;

    EXPORT 
	CurrentLoc, AllocateLabel, TheLabel, EmitLabel, AllocateFiIndex;

    VAR top : LabelType;
	current : CARDINAL;

    PROCEDURE AllocateFiIndex(VAR index : CARDINAL);
    BEGIN
      index := current;
      INC(current);
    END AllocateFiIndex;

    PROCEDURE CurrentLoc() : INTEGER;
      VAR lab : LabelType;
    BEGIN 
      INC(top);
      lab := top;
      BuffS("label");
      BuffCrd(lab);
      WriteObjByte(':'); BuffEol;
      RETURN lab;
    END CurrentLoc;

    PROCEDURE AllocateLabel(VAR lab : LabelType);
    BEGIN
      INC(top);
      lab := top;
    END AllocateLabel;

    PROCEDURE TheLabel(lab : LabelType);
    BEGIN
      BuffS("label");
      BuffCrd(lab);
    END TheLabel;

    PROCEDURE EmitLabel(lab : LabelType);
    BEGIN
      BuffS("label");
      BuffCrd(lab);
      WriteObjByte(':'); BuffEol;
    END EmitLabel;

  BEGIN
    top := 0;
    current := 1;
  END LabelControl;
  (*============================================================*)

  PROCEDURE ResetCodeGen();
  BEGIN
    InitSequence(jumpSeq);
  END ResetCodeGen;

  PROCEDURE InitCodeGen(hsh : HashBucketType);
    VAR index : CARDINAL;
  BEGIN
    StatLinkAttributes();
  END InitCodeGen;

  (*============================================================*)


    PROCEDURE PushAdr(id   : IdDesc;
                      mode : AccessMode);
      TYPE  FSet    = SET OF FormalClass;
      CONST statics = FSet{static, export, extern};
      VAR   disp    : INTEGER;
    BEGIN
      CASE mode OF
      | unresolved, 	(* assert: is a procedure address *)
        directNonL :
          BuffI(pshAdr); 
	  BuffN(id^.linkName);
      | directLocl :
          IF id^.varClass IN statics THEN
            BuffI(pshAdr); 
	    BuffN(id^.linkName);
          ELSE (* stack relative *)
	(*
	 *  IF id^.varClass = auto THEN
	 *    BuffI(pshLP); BuffInt(id^.varOffset); 
	 *  ELSE
	 *    BuffI(pshAP); BuffInt(id^.varOffset); 
	 *    IF id^.varClass = varForm THEN
	 *	BuffEol;
	 *	BuffI(derefW);
	 *    END;
	 *  END;
	 *)
(* ---- *)
            BuffI(pshFP); 
            BuffInt(id^.varOffset); 
	    IF id^.varClass = varForm THEN (* param was optimized *)
	      BuffEol;
	      BuffI(derefW);
	      IF aliasInf THEN WriteMarker(NIL,unresolved) END;
	    END;
          END; 
(* ---- *)
      | highAccess :
       (*
	* BuffI(pshAP); BuffInt(id^.varOffset); 
	*)
          BuffI(pshFP); BuffInt(id^.varOffset); 
      | indirect   : (* all VAR pars, with relative accesses *)
          disp := id^.varOffset;
	  IF id^.name = withTmp THEN 
	    BuffI(pshTmp);
	    BuffCrd(-disp); 
	  ELSE
       (*
	*   BuffI(pshAP); BuffInt(id^.varOffset); 
	*)
(* ---- *)
            BuffI(pshFP); BuffInt(id^.varOffset); 
(* ---- *)
	    BuffEol;
	    BuffI(derefW);
	    IF aliasInf THEN WriteMarker(NIL,unresolved) END;
	  END;
      | uplevel, uplevelIndirect :
	(*
	 *IF id^.varClass = auto THEN
	 *  BuffI(pshLDsp); 
	 *ELSE
	 *  BuffI(pshADsp);
	 *END;
	 *)
(* ---- *)
          BuffI(pshDsp); 
(* ---- *)
	  BuffCrd(id^.lexLev - 1); 
	  Space();
          BuffInt(id^.varOffset);
          (*
           *  Adr of stack frame is now on top of stack
           *
           *  In the case of uplevel value arrays the
           *  offset is not known, so the array must be
           *  accessed indirectly via the parameter
           *)
          IF (mode = uplevelIndirect) OR
             ((id^.varClass = valForm) AND
               IsRefParam(id^.varType)) THEN
	    BuffEol;
            BuffI(derefW); 
	    IF aliasInf THEN WriteMarker(NIL,unresolved) END;
          END;
      END; (* case *)
      BuffEol; 
    END PushAdr;

    PROCEDURE PushRtsAdr(nam : HashBucketType);
    (*
     *  this is used to access m2rts variables
     *)
    BEGIN
      BuffI(pshAdr); 
      BuffN(nam);
      BuffEol; 
    END PushRtsAdr;

    PROCEDURE CreateJumpTable(num : Card16; VAR tab : JumpTabDesc);
      VAR ix : CARDINAL;
    BEGIN (* size ~ 2; locn ~ 2; elems ~ num * 2; *)
      Assert(num <= 4096);
      Storage.ALLOCATE(tab, 4 + num * 2);
      tab^.size := num;
      FOR ix := 0 TO num - 1 DO
	tab^.elems[ix] := 0;
      END;
      AllocateLabel(tab^.locn); (* label of jump table *)
    END CreateJumpTable;

    PROCEDURE DumpJumpTable(tab : JumpTabDesc);
      VAR target : Card16;
          index  : CARDINAL;
    BEGIN
      BuffS(".JUMPTAB ");
      CodeLabel(tab^.locn);
      WriteObjByte(Ascii.ht);
      TheLabel(tab^.elems[0]);
      FOR index := 1 TO tab^.size - 1 DO
        target := tab^.elems[index];
	IF index MOD 4 = 0 THEN 
	  BuffEol; 
	  WriteObjByte(Ascii.ht);
        ELSE Comma;
        END;
        TheLabel(target);
      END;
      BuffEol;
      Storage.DEALLOCATE(tab,4 + tab^.size * 2);
    END DumpJumpTable;

    PROCEDURE EmitJumpTable(tab : JumpTabDesc;
			    def : Card16);
      VAR target : Card16;
          index  : CARDINAL;
    BEGIN
      BuffS("; end of switch");
      BuffEol;
      FOR index := 0 TO tab^.size - 1 DO
        IF tab^.elems[index] = 0 THEN tab^.elems[index] := def END;
      END;
      LinkRight(jumpSeq,tab);
    END EmitJumpTable;

    PROCEDURE PushModName;
    BEGIN
      BuffI(pshAdr);
      BuffS(modNameStr);
      BuffEol;
    END PushModName;

    PROCEDURE PushLit(val : SYSTEM.WORD);
      VAR iVal : INTEGER;
    BEGIN
      iVal := SYSTEM.CAST(INTEGER,val);
      IF iVal = 0 THEN
        BuffI(pshZ);
      ELSE
        BuffI(pshLit);
        BuffInt(iVal);
      END;
      BuffEol;
    END PushLit;

    PROCEDURE PushMemTmp(off : TempIndex);
    BEGIN
(* will become pshLP !!! *)
      BuffI(pshFP);     (* fold ? *)
      BuffInt(tmpOffset + VAL(INTEGER,off)); 
      BuffEol;
    END PushMemTmp;

    PROCEDURE PushCon   (val : INTEGER);
    BEGIN
      BuffI(pshAdr);
      BuffS(conDataStr);
      IF val > 0 THEN
        WriteObjByte('+');
        BuffCrd(val);
      END;
      BuffEol;
    END PushCon;

    PROCEDURE PushTmp   (tmp : TempIndex);
      VAR disp : INTEGER; 
    BEGIN
      disp := tmpOffset + VAL(INTEGER,tmp); 
      BuffI(pshTmp);
      BuffCrd(-disp); 
      BuffEol;
    END PushTmp;

    PROCEDURE Duplicate();
    BEGIN
      BuffI(dup1);
      BuffEol;
    END Duplicate;

    PROCEDURE LineNum    (num : CARDINAL);
    BEGIN
      BuffS("lineNum ");
      BuffCrd(num);
      BuffEol;
    END LineNum;

    PROCEDURE WriteMarker(idn : IdDesc; mod : AccessMode);
      TYPE  MarkerTable = ARRAY AccessMode OF CHAR;
      CONST modeTable   = MarkerTable{"I", "L", "S", "I", "U", "P" BY 3};
		(* unresolved, directLocl, directNonL, highAccess,
                   refOverwrite, indirect, uplevel, uplevelIndirect *)
      CONST statics = FormSet{static, export, extern};
      VAR   ch : CHAR;
    BEGIN
      IF (idn <> NIL) AND 
	 (mod = directLocl) AND
	 (idn^.varClass IN statics) THEN mod := directNonL END;
      ch := modeTable[mod]; 
      IF ch <> "U" THEN
	BuffS("	;@"); WriteObjByte(ch);
	IF idn <> NIL THEN Space; BuffN(idn^.name) END;
      END;
    END WriteMarker;

(*
 *  now the derefs
 *)
    PROCEDURE Deref(obj : Object; idn : IdDesc; mod : AccessMode);
      CONST derefTable = InstructionTable{derefSB,derefUB,derefS16,derefU16,
					derefS32,derefU32,derefW,derefL,
					derefF,derefD};
    BEGIN
      BuffI(derefTable[obj]);
      IF aliasInf THEN WriteMarker(idn,mod) END;
      BuffEol;
    END Deref;

(*
 *  now the pops and assigns
 *)

    PROCEDURE PopNDiscard();
    BEGIN
      BuffI(pop1);
      BuffEol;
    END PopNDiscard;

    PROCEDURE CutParams(W : INTEGER);
    (* pops W bytes from the concrete stack   *)
    BEGIN
      IF W <> 0 THEN		(* jl Oct 94 *)
        BuffI(cutPars);
        BuffInt(W);
        BuffEol;
      END;
    END CutParams;

    PROCEDURE CopyRecord(size  : CARDINAL;
			 ofst  : INTEGER;
    			 aMask : CHAR);
    BEGIN
      BuffI(blkPar);
      BuffCrd(size);
      Comma;
      BuffInt(ofst);
      Comma;
      BuffCrd(ORD(aMask) + 1);
      BuffEol;
    END CopyRecord;

    PROCEDURE PushDstPointer(isRec : BOOLEAN);
    BEGIN
      IF (isRec AND extRecRetPtr) OR
	 (NOT isRec AND extArrRetPtr) THEN
	BuffI(pshDstP);
      ELSE
(* will become pshAP 0 !!! *)
	BuffI(pshFP); 
	BuffInt(destOffset);
        BuffEol;
	BuffI(derefW);
      END;
      BuffEol;
    END PushDstPointer;

    (* post : top of stack is moved to the destination ptr loc  *)
    PROCEDURE MakeDstPointer(size  : CARDINAL;
			     isRec : BOOLEAN);
    BEGIN
      IF (isRec AND extRecRetPtr) OR
	 (NOT isRec AND extArrRetPtr) THEN
	BuffI(mkDstP);
	BuffCrd(size);
        BuffEol;
      ELSE
	AdjustParam(bytesInWord,0);
      END;
    END MakeDstPointer;

    PROCEDURE AdjustParam(size   : Card8;
			  offset : INTEGER);
    BEGIN
      BuffI(mkPar);
      BuffCrd(size);
      Comma;
      BuffInt(offset);
      BuffEol;
    END AdjustParam;

    PROCEDURE MakeFpParam(size   : Card8;
			  offset : INTEGER);
    BEGIN
      BuffI(mkPar);
      BuffCrd(size);
      Comma;
      BuffInt(offset);
      IF parsFixed THEN BuffS(" fpParam") END;
      BuffEol;
    END MakeFpParam;

    PROCEDURE Assign(obj : Object; idn : IdDesc; mod : AccessMode);
      CONST assignTable = InstructionTable{assignB,assignB,assign16,assign16,
			    assign32,assign32,assignW,assignL,assignF,assignD};
    BEGIN
      BuffI(assignTable[obj]);
      IF aliasInf THEN WriteMarker(idn,mod) END;
      BuffEol;
    END Assign;

    PROCEDURE ReverseAssign(obj : Object; idn : IdDesc; mod : AccessMode);
    BEGIN
      BuffI(swap);
      BuffEol;
      Assign(obj,idn,mod);
    END ReverseAssign;

    PROCEDURE CopyBlock(align : CHAR);
    BEGIN
      BuffI(blkCp);
      BuffCrd(ORD(align) + 1);
      BuffEol;
    END CopyBlock;

    PROCEDURE StrLength();
    BEGIN
      BuffI(call);
      BuffN(strLen);
      Comma;
      BuffCrd(2);
      BuffEol;
      IF NOT parsFixed THEN CutParams(2 * bytesInWord) END;
      BuffI(pshRetW);
      BuffEol;
    END StrLength;

(*
 *  now the temporary manipulations
 *)

    PROCEDURE PushFi(ix : CARDINAL);
    BEGIN
      Assert(FALSE);
    END PushFi;

    PROCEDURE PopFi(ix : CARDINAL);
    BEGIN
      Assert(FALSE);
    END PopFi;

    PROCEDURE MakeTemp(tix : TempIndex);
    (* post : the element on tos is associated with temp tix *)
      VAR disp : INTEGER;
    BEGIN
      disp := tmpOffset + VAL(INTEGER,tix);
      BuffI(mkTmp);
      BuffInt(-disp); 
      BuffEol;
    END MakeTemp;

    PROCEDURE MakeWith(dummy : IdDesc;
                        tix  : TempIndex);
      VAR disp : INTEGER;
    BEGIN
      disp := tmpOffset + VAL(INTEGER,tix);
      BuffI(mkTmp);
      BuffCrd(-disp);
      BuffEol;
      BuffI(pop1);
      (*
       *  now set offset for with relative accesses
       *)
      BuffEol;
      dummy^.varOffset := disp;
      Assert(dummy^.name = anonBkt);
      dummy^.name := withTmp;
    END MakeWith;

(*
 *  now the branches and label manipulations
 *)

    PROCEDURE Switch(lab : LabelType); (* used for computed gotos *)
    (* pre  : a dcode address is on the top of stack and loaded  *)
    (* post : jump is taken unconditionally. Pop(1)             *)
    BEGIN
      BuffI(switch); TheLabel(lab);
      BuffEol;
    END Switch;

    PROCEDURE LoopLabel(sno : LabelType);
    BEGIN
      BuffS(".LOOP ");
      EmitLabel(sno);
    END LoopLabel;

    PROCEDURE LoopEnd(sno : LabelType);
    BEGIN
      BuffS(".ENDLOOP ");
      BuffCrd(sno);
      BuffEol;
    END LoopEnd;

    PROCEDURE CodeLabel(sno : LabelType);
    BEGIN
      EmitLabel(sno);
    END CodeLabel;

    PROCEDURE Branch(lab : LabelType);
    BEGIN
    (* post : unconditional branch to lab is emitted            *)
      IF lab <> fallThrough THEN
          BuffI(branch);
          TheLabel(lab);
          BuffEol;
      END;
    END Branch;

    PROCEDURE BranchEQZ(lab : LabelType);
    BEGIN
      BuffI(brFalse);
      TheLabel(lab);
      BuffEol;
    END BranchEQZ;

    PROCEDURE BranchNEZ(lab : LabelType);
    (* pre  : a word (possibly Boolean) is on top of the stack  *)
    (* post : branch taken if equal/not equal to zero. Pop(1)   *)
    BEGIN
      BuffI(brTrue);
      TheLabel(lab);
      BuffEol;
    END BranchNEZ;

    PROCEDURE PushBool(fLab, tLab : LabelType;
		       mergeVar   : IdDesc);
    (* post : branches to fLab leave FALSE on top of stack      *)
    (*        branches to tLab leave TRUE on top of stack       *)
      VAR xLab : LabelType;
    BEGIN
      AllocateLabel(xLab);
      IF fLab = fallThrough THEN
        BuffI(pshZ); BuffEol;
	BuffI(pshFP); BuffInt(mergeVar^.varOffset); BuffEol;
        BuffI(assignB); BuffEol;
        Branch(xLab);
        EmitLabel(tLab);
        BuffI(pshLit); BuffInt(1); BuffEol;
      ELSE
	IF tLab <> fallThrough THEN EmitLabel(tLab) END;
        BuffI(pshLit); BuffInt(1); BuffEol;
	BuffI(pshFP); BuffInt(mergeVar^.varOffset); BuffEol;
        BuffI(assignB); BuffEol;
        Branch(xLab);
        EmitLabel(fLab);
        BuffI(pshZ); BuffEol;
      END;
      BuffI(pshFP); BuffInt(mergeVar^.varOffset); BuffEol;
      BuffI(assignB); BuffEol;
      EmitLabel(xLab);
      BuffI(pshFP); BuffInt(mergeVar^.varOffset); BuffEol;
      BuffI(derefUB); BuffEol;
    END PushBool;

(*
 *  now the procedure call operations
 *  object size is not needed for 32-bit native versions
 *  but IS needed to link to turbo-C etc.
 *)

    PROCEDURE PushResult(obj : Object);
      CONST pshTable = InstructionTable{pshRetSB,pshRetUB,pshRetS16,pshRetU16,
			  pshRetS32,pshRetU32,pshRetW,pshRetL,pshRetF,pshRetD};
    BEGIN
      BuffI(pshTable[obj]);
      BuffEol;
    END PushResult;

(* =========================================== *)

    PROCEDURE CallTOSFunc(byt : INTEGER;
                          obj : Object;
			  num : CARDINAL);
    BEGIN
      BuffI(popCall);
      BuffCrd(num);
      BuffEol;
      CutParams(byt);
      BuffEol;
      PushResult(obj);
    END CallTOSFunc;

    PROCEDURE CallFunc(name : HashBucketType;
		        byt : INTEGER;
                        obj : Object;
			num : CARDINAL);
    (* post : a call to the procedure is emitted                *)
    (*        in the case of function calls ret val is tos      *)
    BEGIN
      BuffI(call);
      BuffN(name);
      Comma;
      BuffCrd(num);
      BuffEol;
      CutParams(byt);
      PushResult(obj);
    END CallFunc;

    PROCEDURE CallProc(name : HashBucketType;
		        byt : INTEGER;
			num : CARDINAL);
    (* post : a call to the procedure is emitted                *)
    (*        in the case of function calls ret val is tos      *)
    BEGIN
      BuffI(call);
      BuffN(name);
      Comma;
      BuffCrd(num);
      BuffEol;
      CutParams(byt);
    END CallProc;

    PROCEDURE CallTOSProc(byt : INTEGER;
			  num : CARDINAL);
    (* post : a call to the procedure is emitted                *)
    (*        in the case of function calls ret val is tos      *)
    BEGIN
      BuffI(popCall);
      BuffCrd(num);
      BuffEol;
      CutParams(byt);
    END CallTOSProc;

    PROCEDURE RTSfunc(trp : HashBucketType;
		      obj : Object;
		      num : CARDINAL);
    (* emits a call to the runtime system function "trp"  *)
    BEGIN
      BuffI(call);
      BuffN(trp);
      Comma;
      BuffCrd(num);
      BuffEol;
      IF NOT parsFixed THEN CutParams(num * bytesInWord) END;
      PushResult(obj);
    END RTSfunc;

    PROCEDURE RTSproc(trp  : HashBucketType;
		      num  : CARDINAL);
    (* emits a call to the runtime system procedure "trp" *)
    BEGIN
(*
 * actually, to fit with other calls,
 * the call should be a subroutine jump
 *)
      BuffI(call);
      BuffN(trp);
      Comma;
      BuffCrd(num);
      BuffEol;
      IF NOT parsFixed THEN CutParams(num * bytesInWord) END;
    END RTSproc;

    PROCEDURE Trap(trp : HashBucketType;
		   num : CARDINAL);
    (* emits a call to "trp", and does not expect return  *)
    BEGIN
      BuffI(trap);
      BuffN(trp);
      Comma;
      BuffCrd(num);
      BuffEol;
    END Trap;

(*
 *  now the procedure entry and exit operations
 *)

    PROCEDURE CopyArrays(id : IdDesc);
      VAR curs : ElemPtr;
          elem : FormalType;
	  expd : ExpandInfo;
          pram : IdDesc;
          offs : INTEGER;
	  open : CARDINAL;
	  elTp : TypeDesc;
    BEGIN
(*
 *    offs := copyOffset;
 *)
      offs := 0;
      InitCursor(id^.body^.adjustSeq,curs);
      WHILE NOT Ended(curs) DO
	GetNext(curs,expd);
        BuffS("  .EXPAND");
	IF expd^.dimenNum > 1 THEN
	  WriteObjByte("("); BuffCrd(expd^.dimenNum); WriteObjByte(")");
	END;
	Space();
        BuffInt(expd^.mrshNode^.actualX^.name.variable^.varOffset); 
	Comma();
	BuffInt(expd^.mrshNode^.mrshPtr^.name.variable^.varOffset);
	BuffS(" .SIZE ");
        BuffCrd(expd^.elemType^.size);
	BuffS(" .ALIGN ");
        BuffCrd(ORD(expd^.elemType^.alignMask) + 1);
	BuffEol;
      END;

      InitCursor(id^.procType^.params,curs);
      WHILE NOT Ended(curs) DO
        GetNext(curs,elem);
	IF (elem^.form = valForm) AND IsCopyParam(elem^.type) THEN
          LookupInThisScope(id^.scope,elem^.fNam,pram);
	 (* 
	  * push array size, uplevel flag, destination address (offset from 
	  * bp) and source address (offset from bp) then call procedure in 
	  * interpreter to copy the value array  
	  *)
	  pram^.ptrOffset := pram^.varOffset;
	  (* must align *)
	  offs := Align(offs,elem^.type^.alignMask);
	  BuffS("  .COPY ");
          BuffInt(pram^.varOffset);
	  Comma();
          BuffInt(copyOffset + offs);
	  BuffS(" .SIZE ");
          BuffCrd(pram^.varType^.size);
	  BuffS(" .ALIGN ");
          BuffCrd(ORD(elem^.type^.alignMask) + 1);
	  BuffEol;
          pram^.varOffset := copyOffset + offs;
          INC(offs,elem^.type^.size);
	ELSIF (elem^.form < openValForm) AND
	       IsRefParam(elem^.type) THEN
	 (*
	  *  Here we warp the formal parameter so as
	  *  to be treated as a variable parameter
	  *)
          LookupInThisScope(id^.scope,elem^.fNam,pram);
	  pram^.varClass := varForm;
        END;
      END;
    END CopyArrays;

   (* ------------------------------------- *)
    PROCEDURE LocalInfo(scope : IdTree);

      PROCEDURE WriteLocal(name  : HashBucketType;
			   ofst  : INTEGER;
			   size  : CARDINAL;
			   sufx  : ARRAY OF CHAR);

        CONST conS = "  .LOCAL _";
	      excS = "  .EXCEPT _";
        VAR str : StringType;
	    idx : CARDINAL;
	    pdx : CARDINAL;
	    chr : CHAR;
      BEGIN
	pdx := 0;
	IF exceptionDescriptor IN scope^.ident^.varUseSet THEN
	  str := excS;
	ELSE
	  str := conS;
	END;
	idx := LENGTH(conS);
	GetSourceRep(name,str,idx);	(* updates idx!  *)
	REPEAT
	  chr := sufx[pdx];		(* copy up to "" *)
	  str[idx] := chr;
	  INC(idx); INC(pdx);
	UNTIL chr = "";
	BuffS(str); Space;
	BuffInt(ofst); Comma;
	BuffCrd(size); Space;
      END WriteLocal;

      CONST empty = "(0,0,0)";

      VAR siz  : CARDINAL;
	  pars : ARRAY [0 .. 7] OF CHAR;
	  hiXt : ARRAY [0 .. 7] OF CHAR;
	  hiDs : IdDesc;
    BEGIN
      IF scope <> NIL THEN
        WITH scope^.ident^ DO
	  IF  idClass = varNode THEN
	    IF debugOn AND gdbSupport THEN EmitTypeDef(varType) END;
	    pars := empty;
	    IF uplevAcc IN varUseSet THEN pars[1] := "1" END;
	    CASE varClass OF
	    | static, export, extern : (* skip *)
	    | varForm     : 
		WriteLocal(name,varOffset,adrSize,""); BuffS(pars);
	        IF debugOn AND gdbSupport THEN EmitLocal(varType,TRUE) END;
	        BuffEol;
	    | openValForm,openVarForm :
	        hiXt := "$hi0"; 
		WriteLocal(name,varOffset,adrSize,""); BuffS(pars); 
	        IF debugOn AND gdbSupport THEN EmitLocal(varType,TRUE) END;
		BuffEol;
		hiDs := nextHigh;
		WHILE hiDs <> NIL DO
		  INC(hiXt[3]);
		  IF hiXt[3] > '9' THEN hiXt[3] := '0'; INC(hiXt[2]) END;
		  WriteLocal(name,hiDs^.varOffset, 
					bytesInWord,hiXt); BuffS(pars);
	          IF debugOn AND gdbSupport THEN EmitLocal(hiType,FALSE) END;
	          BuffEol;
		  hiDs := hiDs^.nextHigh;
		END;
	    ELSE (* value params *)
	      IF uplevThr IN varUseSet THEN pars[3] := "1" END;
	      IF varType^.tyClass IN strucClasses THEN pars[1] := "1" END;
	     (*
	      *  There is a kludge here that structured classes must
	      *  have the pointer threat attribute set, so that internal
	      *  aliassing is taken into account in any value tracking.
	      *)
	      IF varParThr IN varUseSet THEN 
		pars[5] := "1";
	      END;
	      WriteLocal(name,varOffset,varType^.size,""); BuffS(pars);
	      IF varType^.tyClass IN realClasses THEN 
	       (*
		*  ok to use fpParam for local variables
		*  as of dcode reference version 2.00
		*)
	        BuffS(" fpParam");
	        IF debugOn AND gdbSupport THEN EmitLocal(varType,FALSE) END;
              ELSIF (varClass = valForm) AND
		     IsCopyParam(varType) THEN
	        IF debugOn AND gdbSupport THEN EmitLocal(varType,FALSE) END;
	        BuffEol;
	        WriteLocal(name,ptrOffset,adrSize,"$ptr"); BuffS(pars);
	        IF debugOn AND gdbSupport THEN EmitLocal(varType,TRUE) END;
	      ELSE
	        IF debugOn AND gdbSupport THEN EmitLocal(varType,FALSE) END;
	      END;
	      BuffEol;
	    END;
         (*
	  *  the following code ensures that a .LOCAL appears
	  *  for the anonymous parameter which is needed for 
	  *  functions returning structured types ... 
	  *)
	  ELSIF idClass = unknown THEN (* mark return dummy *)
	    BuffS('  .LOCAL _$ret_ ');
	    BuffCrd(stackMarkSize); WriteObjByte(","); BuffCrd(adrSize);
	    BuffS(' (0,0,0)'); BuffEol;
	  END;
	END;
	LocalInfo(scope^.left); LocalInfo(scope^.right);
      END;
    END LocalInfo;
   (* ------------------------------------- *)

    PROCEDURE EntryEpilog(id : IdDesc);
      VAR lexLev, disp : CARDINAL;
    BEGIN
      WriteObjByte("(");
      aliasInf := optimize IN id^.body^.callAttrib;
      IF stackCheck IN id^.body^.callAttrib THEN
        BuffS(".CHECK,.SIZE=");
      ELSE BuffS(".NOCHECK,.SIZE=");
      END;
      BuffCrd(-copyOffset);
      IF hasUplevObj IN id^.body^.callAttrib THEN
	BuffS(",.DISPLAY:");
        BuffCrd(LexLevel(id));
      ELSE BuffS(",.NODISPLAY");
      END;
      IF parsFixed THEN
	BuffS(",.ASSEMBLY=");
	BuffCrd(id^.body^.maxParSize);
      END;
      IF (id <> thisCompileUnit) AND
	 (retCutAll IN modState) THEN
	BuffS(",.RETCUT=");
	BuffCrd(id^.procType^.parSiz);
      END;
      WriteObjByte(")");
      BuffEol;
      (*
       *  do whatever stack adjustment and copy whatever values
       *)
      IF id <> thisCompileUnit THEN CopyArrays(id) END;
      LocalInfo(id^.scope);
    END EntryEpilog;

    PROCEDURE GenerateEntry(id : IdDesc);
    (* pre  : id has all info needed for stack frame generation *)
    (* post : proc state is evaluated, entry pseudo's emitted   *)
    (*        value arrays are copied and any soapspace fetched *)
      VAR name : HashBucketType;
    BEGIN
      BuffEol;
      ResetCodeGen();
      IF id = thisCompileUnit THEN 
        name := callSmbl;
      ELSE
        name := id^.linkName;
      END;
      IF debugOn AND gdbSupport THEN EmitObject(id) END;
      BuffS(".PROC ");
      BuffN(name);
      SetCurrentEnv(id);
(*
 *  only for iapx86 with 16-bit segments!
 *
 *    Assert(-copyOffset < 32768, "!!!FRAME_SIZE_ERROR!!!");
 *)
      EntryEpilog(id);
      BuffS(".ENTRY"); 
      BuffEol;
      LineNum(id^.body^.headerLine);
    END GenerateEntry;

    PROCEDURE PushDescAndCall(exceptDesc : IdDesc; name : ARRAY OF CHAR);
    BEGIN
      BuffI(pshFP); BuffInt(exceptDesc^.varOffset); 
      BuffEol;
      BuffI(derefW);
      BuffEol;
      AdjustParam(bytesInWord,0);
      BuffI(call); BuffS(name); BuffS(",1");
      BuffEol;
    END PushDescAndCall;

    PROCEDURE FreeDescriptor(exceptDesc : IdDesc);
    BEGIN
      PushDescAndCall(exceptDesc, "__gp_FreeDescriptor");
    END FreeDescriptor;

    PROCEDURE PropagateException(id : IdDesc; exceptDesc : IdDesc);
    BEGIN
      LineNum(id^.body^.endIdLine);
      PushDescAndCall(exceptDesc, "__gp_PropagateException");
    END PropagateException;

    PROCEDURE GenerateExit(id : IdDesc; labS : LabString);
    (* post : entry reg-save code is emitted and code buffer    *)
    (*        dumped, soap is released, saved regs restored,    *)
    (*        and the exit code emitted                         *)
      VAR curs  : ElemPtr;
	  tab   : JumpTabDesc;
	  index : INTEGER;
    BEGIN
      IF id = thisCompileUnit THEN BuffI(endF) ELSE BuffI(endP) END;
      BuffEol;
      (* jump tables here *)
      InitCursor(jumpSeq,curs);
      WHILE NOT Ended(curs) DO
        GetNext(curs,tab);
        DumpJumpTable(tab);
      END;
      DisposeList(jumpSeq);
     (* except tables here *)
      Assert((HIGH(labS)+1) MOD 3 = 0);
      FOR index := 0 TO HIGH(labS) - 2 BY 3 DO
	BuffS(".EXCEPT "); 
        TheLabel(labS[index]);     Comma;
        TheLabel(labS[index + 1]); Comma;
        TheLabel(labS[index + 2]); BuffEol; 
      END;
      IF exceptOK THEN
        BuffS(".EXCEPT "); 
        IF id = thisCompileUnit THEN BuffN(callSmbl) ELSE BuffN(id^.name) END;
        BuffEol;
      END;
      BuffS(".ENDP"); 
      BuffEol;
    END GenerateExit;

    PROCEDURE MakeRetValue(obj : Object);
    BEGIN
      IF obj = double THEN  (* changed for gp2d *)
        BuffI(popRetD);
      ELSIF obj = float THEN
        BuffI(popRetF);
      ELSIF obj = hugeInt THEN
        BuffI(popRetL);
      ELSE
        BuffI(popRetW);
      END;
      BuffEol;
    END MakeRetValue;

    PROCEDURE GenerateReturn();
    BEGIN
      BuffI(exit);
      BuffEol;
    END GenerateReturn;

(*
 *  now the operations
 *  for all binops, the right op is tos, left under that
 *  for unary ops, operand is on tos
 *)

    PROCEDURE NegateInt(test : BOOLEAN);
    BEGIN
      BuffI(negate);
      IF test THEN BuffS(intOverS) END;
      BuffEol;
    END NegateInt;

    PROCEDURE NegateBool;
    BEGIN
      BuffI(boolNeg);
      BuffEol;
    END NegateBool;

(*
 *  herewith the fp code (kjg 20-Jun-91)
 *)
    PROCEDURE NegateFlt;
    BEGIN
      BuffI(negFlt);
      BuffEol;
    END NegateFlt;

    PROCEDURE NegateDbl;
    BEGIN
      BuffI(negDbl);
      BuffEol;
    END NegateDbl;

    PROCEDURE AddDbl;
    BEGIN
      BuffI(addDbl);
      BuffEol;
    END AddDbl;

    PROCEDURE SubDbl;
    BEGIN
      BuffI(subDbl);
      BuffEol;
    END SubDbl;

    PROCEDURE MulDbl;
    BEGIN
      BuffI(mulDbl);
      BuffEol;
    END MulDbl;

    PROCEDURE SlashDbl;
    BEGIN
      BuffI(divDbl);
      BuffEol;
    END SlashDbl;

    PROCEDURE AddFlt;
    BEGIN
      BuffI(addFlt);
      BuffEol;
    END AddFlt;

    PROCEDURE SubFlt;
    BEGIN
      BuffI(subFlt);
      BuffEol;
    END SubFlt;

    PROCEDURE MulFlt;
    BEGIN
      BuffI(mulFlt);
      BuffEol;
    END MulFlt;

    PROCEDURE SlashFlt;
    BEGIN
      BuffI(divFlt);
      BuffEol;
    END SlashFlt;

    PROCEDURE DFloat;
    BEGIN
      BuffI(uToDbl);
      BuffEol;
    END DFloat;

    PROCEDURE FFloat;
    BEGIN
      BuffI(uToFlt);
      BuffEol;
    END FFloat;

    PROCEDURE TruncF(mode : ModeEnum);
    BEGIN
      BuffI(fTrunc);
      BuffS(modeStr[mode]);
      BuffEol;
    END TruncF;

    PROCEDURE TruncD(mode : ModeEnum);
    BEGIN
      BuffI(dTrunc);
      BuffS(modeStr[mode]);
      BuffEol;
    END TruncD;

    PROCEDURE FloorF(test : BOOLEAN);
    BEGIN
      BuffI(fFloor);
      IF test THEN BuffS(intOverS) END;
      BuffEol;
    END FloorF;

    PROCEDURE FloorD(test : BOOLEAN);
    BEGIN
      BuffI(dFloor);
      IF test THEN BuffS(intOverS) END;
      BuffEol;
    END FloorD;

    PROCEDURE RoundF(test : BOOLEAN);
    BEGIN
      BuffI(fRound);
      IF test THEN BuffS(intOverS) END;
      BuffEol;
    END RoundF;

    PROCEDURE RoundD(test : BOOLEAN);
    BEGIN
      BuffI(dRound);
      IF test THEN BuffS(intOverS) END;
      BuffEol;
    END RoundD;

    PROCEDURE FtoD;
    BEGIN
      BuffI(fToDbl);
      BuffEol;
    END FtoD;

    PROCEDURE DtoF;
    BEGIN
      BuffI(dToFlt);
      BuffEol;
    END DtoF;

    PROCEDURE ItoF;
    BEGIN
      BuffI(iToFlt);
      BuffEol;
    END ItoF;

    PROCEDURE ItoD;
    BEGIN
      BuffI(iToDbl);
      BuffEol;
    END ItoD;

(* ---------------------------------------- *)

    PROCEDURE AbsInt(test : BOOLEAN);
    BEGIN
      BuffI(abs);
      IF test THEN BuffS(intOverS) END;
      BuffEol;
    END AbsInt;

    PROCEDURE AbsFlt;
    BEGIN
      BuffI(absFlt);
      BuffEol;
    END AbsFlt;

    PROCEDURE AbsDbl;
    BEGIN
      BuffI(absDbl);
      BuffEol;
    END AbsDbl;

    PROCEDURE AddAdr();
    BEGIN
      BuffI(addAdr);
      BuffEol;
    END AddAdr;

    PROCEDURE FlattenAdr();
    BEGIN
      BuffI(flatten);
      BuffEol;
    END FlattenAdr;

    PROCEDURE AddOffset(off : INTEGER);
    BEGIN
      IF off <> 0 THEN
      (* $R- *)
        BuffI(addOff);
        BuffInt(off);
        BuffEol;
      (* $R= *)
      END;
    END AddOffset;

    PROCEDURE Add(mode : ModeEnum);
    BEGIN
      BuffI(add);
      BuffS(modeStr[mode]);
      BuffEol;
    END Add;

    PROCEDURE Sub(mode : ModeEnum);
    BEGIN
      BuffI(sub);
      BuffS(modeStr[mode]);
      BuffEol;
    END Sub;

    PROCEDURE Mul(mode : ModeEnum);
    BEGIN
      BuffI(mul);
      BuffS(modeStr[mode]);
      BuffEol;
    END Mul;

(* 22-1-91 test flag removed - always trap for Div, Mod, Rem and Slash *)

    PROCEDURE Div(mode : ModeEnum);
    BEGIN
      BuffI(div);
      BuffS(modeStr[mode]);
      BuffEol;
    END Div;

    PROCEDURE Mod(mode : ModeEnum);
    BEGIN
      BuffI(mod);
      BuffS(modeStr[mode]);
      BuffEol;
    END Mod;

    PROCEDURE Rem(mode : ModeEnum);
    BEGIN
      BuffI(rem);
      BuffS(modeStr[mode]);
      BuffEol;
    END Rem;

    PROCEDURE Slash(mode : ModeEnum);
    BEGIN
      BuffI(slash);
      BuffS(modeStr[mode]);
      BuffEol;
    END Slash;

(*
 *  Bitwise operations
 *)

    PROCEDURE BitNegate;  (* Pop(0) *)
    BEGIN
      BuffI(bitNeg);
      BuffEol;
    END BitNegate;

    PROCEDURE BitAND;     (* Pop(1) *)
    BEGIN
      BuffI(andWrd);
      BuffEol;
    END BitAND;

    PROCEDURE BitXOR;     (* Pop(1) *)
    BEGIN
      BuffI(xorWrd);
      BuffEol;
    END BitXOR;

    PROCEDURE BitOR;      (* Pop(1) *)
    BEGIN
      BuffI(orWrd);
      BuffEol;
    END BitOR;

    PROCEDURE Shift;
    BEGIN
      BuffI(shiftV);
      BuffEol;
    END Shift;

    PROCEDURE Rotate;
    BEGIN
      BuffI(rotate);
      BuffEol;
    END Rotate;

    PROCEDURE LeftShift;
    (* for small numbers Op(1) yields tos <- tos * 2. Pop(1)    *)
    BEGIN
      BuffI(shLeft);
      BuffEol;
    END LeftShift;

(*
 *  relops producing Boolean results. All operations Pop(1)
 *)
    TYPE   ExprNodeMap = ARRAY [0 .. 6] OF Relops;
    CONST  exprNodeToRelop = ExprNodeMap
                {eqR, neR, gtR, geR, lsR, leR, inR};
           eqOrd = ORD(equalsNode);

    PROCEDURE SetInOp;
    BEGIN
      BuffI(setIn);
      BuffEol;
    END SetInOp;

    PROCEDURE SetIncl;
    BEGIN
      BuffI(setIncl);
      BuffEol;
    END SetIncl;

    PROCEDURE SetExcl;
    BEGIN
      BuffI(setExcl);
      BuffEol;
    END SetExcl;

    PROCEDURE SetRelop (op : ExprNodeClass);  (* word sets *)
    VAR
      operator : Relops;
    BEGIN
      operator := exprNodeToRelop[ORD(op) - eqOrd];
      CASE operator OF
        | geR : BuffI(setGE); 
        | leR : BuffI(setLE);
        | eqR : BuffI(relEQ);
        | neR : BuffI(relNE); 
      END;
      BuffEol;
    END SetRelop;

    PROCEDURE CardRelop(op : ExprNodeClass);
      CONST cardRelopTable = RelopTable{crdLS,crdLE,relEQ,
                             crdGT,crdGE,relNE};
    BEGIN
      BuffI(cardRelopTable[ORD(exprNodeToRelop[ORD(op) - eqOrd])]);
      BuffEol;
    END CardRelop;

    PROCEDURE IntRelop (op : ExprNodeClass);
      CONST intRelopTable = RelopTable{intLS,intLE,relEQ,
                            intGT,intGE,relNE};
    BEGIN
      BuffI(intRelopTable[ORD(exprNodeToRelop[ORD(op) - eqOrd])]);
      BuffEol;
    END IntRelop;

    PROCEDURE SRealRelop(op : ExprNodeClass);
    BEGIN
      BuffI(fltRel);
      BuffRelEol(exprNodeToRelop[ORD(op) - eqOrd]);
    END SRealRelop;

    PROCEDURE RealRelop(op : ExprNodeClass);
    BEGIN
      BuffI(dblRel);
      BuffRelEol(exprNodeToRelop[ORD(op) - eqOrd]);
    END RealRelop;

    PROCEDURE HugeRelop(op : ExprNodeClass);
    BEGIN
      BuffI(longRel);
      BuffRelEol(exprNodeToRelop[ORD(op) - eqOrd]);
    END HugeRelop;

    PROCEDURE MakeWord(mode : ModeEnum);
    BEGIN
      BuffI(lToWrd); 
      BuffS(modeStr[mode]);
      BuffEol;
    END MakeWord;

    PROCEDURE MakeIntLong;
    BEGIN
      BuffI(iToS64); BuffEol;
    END MakeIntLong;

    PROCEDURE MakeCrdLong;
    BEGIN
      BuffI(uToS64); BuffEol;
    END MakeCrdLong;

    PROCEDURE NegateLong(test : BOOLEAN);
    BEGIN
      BuffI(negL); 
      IF test THEN BuffS(intOverS) END;
      BuffEol;
    END NegateLong;

    PROCEDURE MulLong(test : BOOLEAN);
    BEGIN
      BuffI(mulL); 
      IF test THEN BuffS(intOverS) END;
      BuffEol;
    END MulLong;

    PROCEDURE AddLong(test : BOOLEAN);
    BEGIN
      BuffI(addL); 
      IF test THEN BuffS(intOverS) END;
      BuffEol;
    END AddLong;

    PROCEDURE SubLong(test : BOOLEAN);
    BEGIN
      BuffI(subL); 
      IF test THEN BuffS(intOverS) END;
      BuffEol;
    END SubLong;

    PROCEDURE SlashLong;
    BEGIN
      BuffI(slashL); BuffEol;
    END SlashLong;

    PROCEDURE RemLong;
    BEGIN
      BuffI(remL); BuffEol;
    END RemLong;

    PROCEDURE DivLong;
    BEGIN
      BuffI(divL); BuffEol;
    END DivLong;

    PROCEDURE ModLong;
    BEGIN
      BuffI(modL); BuffEol;
    END ModLong;

    PROCEDURE AbsLong(test : BOOLEAN);
    BEGIN
      BuffI(absL); 
      IF test THEN BuffS(intOverS) END;
      BuffEol;
    END AbsLong;

    PROCEDURE HFloat;
    BEGIN
      BuffI(lToDbl); BuffEol;
    END HFloat;

    PROCEDURE HTrunc(test : BOOLEAN);
    BEGIN
      BuffI(dTruncL); 
      IF test THEN BuffS(intOverS) END;
      BuffEol;
    END HTrunc;

    PROCEDURE HRound(test : BOOLEAN);
    BEGIN
      BuffI(dRoundL); 
      IF test THEN BuffS(intOverS) END;
      BuffEol;
    END HRound;

    PROCEDURE HEntier(test : BOOLEAN);
    BEGIN
      BuffI(dFloorL); 
      IF test THEN BuffS(intOverS) END;
      BuffEol;
    END HEntier;

    PROCEDURE BigSetRelop (op : ExprNodeClass);
    (* pre  : the right op is on tos, left op below that        *)
    (* post : tos contains Boolean result of given comparison   *)
    VAR
      operator : Relops;
    BEGIN
      operator := exprNodeToRelop[ORD(op) - eqOrd];
      CASE operator OF
        | eqR : RTSfunc(equ,byteCard,3);
        | neR : RTSfunc(neq,byteCard,3);
        | geR : RTSfunc(geq,byteCard,3);
        | leR : RTSfunc(leq,byteCard,3);
      END;
    END BigSetRelop;

    PROCEDURE EmitTest(name  : HashBucketType;
		       lo,hi : INTEGER);
    BEGIN
      BuffI(dup1); BuffEol;
      BuffI(test);
      BuffN(name); Comma; BuffInt(lo); Comma; BuffInt(hi);
      BuffEol;
    END EmitTest;

    PROCEDURE RngAssert(lo,hi : INTEGER);
    BEGIN
      BuffI(assert); BuffInt(lo); Comma; BuffInt(hi); BuffEol;
    END RngAssert;

(*
 *  PROCEDURE EmitIndexTest(lo,hi : INTEGER);
 *  BEGIN
 *    BuffI(dup1); BuffEol;
 *    BuffI(test);
 *    BuffS("index,"); BuffInt(lo); Comma; BuffInt(hi);
 *    BuffEol;
 *  END EmitIndexTest;
 *
 *  PROCEDURE EmitRangeTest(lo,hi : INTEGER);
 *  BEGIN
 *    BuffI(dup1); BuffEol;
 *    BuffI(test);
 *    BuffS("range,"); BuffInt(lo); Comma; BuffInt(hi);
 *    BuffEol;
 *  END EmitRangeTest;
 *)

    PROCEDURE EmitAssertTest(xLab : LabelType;
			     trap : HashBucketType;
			     rOff : CARDINAL;
			     line : CARDINAL);
    BEGIN
      BuffS("	.TRAP	"); BuffN(trap); Comma; TheLabel(xLab); Comma; 
      IF line = 0 THEN
        BuffS(conDataStr);
        IF rOff > 0 THEN
          WriteObjByte('+');
          BuffCrd(rOff);
	END;
      ELSE
        BuffS(modNameStr);
      END;
      Comma; BuffCrd(line); BuffEol;
    END EmitAssertTest;

END M2DWriter.

