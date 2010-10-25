(****************************************************************)
(*                                                              *)
(*             Modula-2 Compiler Source Module                  *)
(*                                                              *)
(*                 Compile-time Operations                      *)
(*                                                              *)
(*      (c) copyright 1988 Faculty of Information Technology    *)
(*                                                              *)
(*      original module : kjg March 1988                        *)
(*      modifications   : 22-Dec-88 jrh Convert arg NIL test;   *)
(*                                      Documentation           *)
(*                      : 28-Jun-89 jrh / REM DIV MOD logic     *)
(*                      : 29-Jun-89 jrh * output type           *)
(*			: 17-Aug-89 jrh -ve rOp now ok for DIV  *)
(*			: 20-Aug-89 kjg fix of Convert for subr *)
(*			: 28-Aug-89 jrh unary - only signed     *)
(*			: 11-Nov-89 kjg new proc CopyConstant   *)
(*			: 14-Nov-89 kjg new proc ExtractCon     *)
(*			: 20-Feb-90 kjg change to hostType in   *)
(*				        procedure CopyConstant  *)
(*			: 20-Jul-90 kjg fix FOR in CopyConst    *)
(*			: 03-Mar-92 jrh import ConBlock		*)
(*			: 17-Mar-92 kjg Operation: IN result	*)
(*					type; *+- range checks	*)
(*			: 28-May-92 jrh FixUp: cards = 0 => ZZ	*)
(*			: 21-Oct-92 kjg fix for-UL in CopyConst *)
(*								*)
(*   =============== merged mips and i386 source ============	*)
(*			   kjg 22 Mar 93			*)
(*                                                              *)
(****************************************************************
$Log: m2compop.mod,v $
Revision 1.10  1995/10/18 00:37:52  lederman
give error 219 (invalid const op) for DIV, '/', REM, MOD with right op. zero
floating-point overflow gives warning 511

Revision 1.9  1995/05/02 01:47:28  lederman
generate HUGE explicity for x / 0.0, since Alpha doesn't know how to do this

# Revision 1.8  1995/03/17  02:54:20  lederman
# fix string catenation to skip ""
#
# Revision 1.7  1995/02/23  03:44:54  lederman
# add checking of ProgArgs.FP_Overflow for Alpha
#
# Revision 1.6  1994/09/12  00:49:31  gough
# fix subtraction case of Operation, to eliminate spurious errors etc.
#
# Revision 1.5  1994/09/05  02:42:20  gough
# fix semantics of IN as according to ISO DIS
#
# Revision 1.4  1994/07/01  04:00:07  lederman
# fix mult & minus Operations that can change type of result
# fix CopyConstant & ExtractConstant for 64-bit words
# -- subranges now handled as part of numeric types in general
#
# Revision 1.3  1994/06/07  06:29:18  gough
# use new module "Safe" for compile time operations
#
# Revision 1.2  1994/04/28  00:39:25  gough
# add hiddens to CopyConst, adrs etc to ExtractConst for NIL value
#
# Revision 1.1  1994/04/07  04:44:59  lederman
# Initial revision
#
*****************************************************************
Revision 1.5  94/03/24  18:24:41  gough
allow for address components in CopyConstant (only NIL of course)
assignment of proctypes and non-const adrs is ok in runtime constructors.

Revision 1.4  94/03/23  14:47:37  gough
careful range checking on all compile time operations.
*****************************************************************)

IMPLEMENTATION MODULE M2CompOperations;

(*
 * IMPORT StdError;
 *)
 
IMPORT Safe;  (* safe arithmetic operations *)

FROM Types IMPORT Int8;

FROM SYSTEM IMPORT CAST, WORD;
FROM M2NodeDefs  IMPORT TypeDesc, TyNodeClass, TyClassSet;
FROM ProgArgs IMPORT Assert, FP_Overflow;
FROM M2InOut IMPORT AbortMessage, Error;
FROM M2TabInitialize IMPORT PointerTo;
FROM M2SSUtilities IMPORT IsSignedType, Compatible, OrdinalValue;

FROM M2Alphabets IMPORT 
	Spellix, LexAttType, ConBlock, TerminalSymbols, SymbolSet;

FROM M2NameHandler IMPORT 
	SetOperate, SetRelop, SetInOp, Commit,
	StringTable, MarkInterimSpellix, CopyChar, InterimSpellix;

FROM M2MachineConstants IMPORT 
	intMax, charMax, bytesInWord, adrSize, INFINITY,
	(* extras for gp2d *) crossEndian, bigEndian;


    PROCEDURE Negate(VAR type : TypeDesc;
                     VAR val  : LexAttType);
    (* 
     *  Negate value val of type type.
     *
     *  If type is not a signed type, the type
     *  is changed and a range check performed.
     *)
    BEGIN
      IF type <> NIL THEN
        CASE type^.tyClass OF
          RR, doubles, floats : 
	    val.floatValue := - val.floatValue;
        | II : 
	    IF val.intValue = MIN(INTEGER) THEN
	      val.fixValue := MAX(INTEGER) + 1;
              type := PointerTo(UU);
	    ELSE
	      val.intValue := - val.intValue;
	      type := PointerTo(ZZ);
	    END;
        | ZZ : 
	    IF val.intValue <> 0 THEN
	      val.intValue := - val.intValue;
              type := PointerTo(II);
	    END;
        | UU : 
	    Assert(val.fixValue > MAX(INTEGER)); (* was intMax - jl Jun 94 *)
	    IF val.fixValue = (MAX(INTEGER) + 1) THEN
	      val.intValue := MIN(INTEGER);
	      type := PointerTo(II);
	    ELSE
              Error(215); type := NIL;
	    END;
        | ints :
            IF val.intValue < 0 THEN 
	      type := PointerTo(II);
            ELSE 
              type := PointerTo(ZZ);
            END;
            Negate(type,val);  (* tail recursion ! *)
        | subranges :
            type := type^.hostType;
            Negate(type,val);  (* tail recursion ! *)
        ELSE Error(268); type := NIL;
        END;
      END;
    END Negate;

    PROCEDURE BoolOps(opr : TerminalSymbols;
                  VAR lOp : CARDINAL;
                      rOp : CARDINAL);
    (*
     *  Perform binary operation here both operands are Boolean. The result
     *  replaces the left operand.
     *
     *  Called only from Operation, which in turn is only called with constant 
     *  operands.
     *)
    BEGIN
      CASE opr OF
        andSy   : lOp := ORD((lOp + rOp) = 2);
      | orSy    : lOp := ORD((lOp + rOp) # 0);
      | equals  : lOp := ORD(lOp = rOp);
      | notEq   : lOp := ORD(lOp # rOp);
      | greater : lOp := ORD(lOp > rOp);
      | grEqual : lOp := ORD(lOp >= rOp);
      | less    : lOp := ORD(lOp < rOp);
      | lessEq  : lOp := ORD(lOp <= rOp);
      ELSE Error(219);
      END;
    END BoolOps;

    PROCEDURE FixUp(class   : TyNodeClass;
                    operand : LexAttType;
                VAR opType  : TypeDesc);
    (*
     *  Map all valid opTypes to the range II..chars.
     *  Class is simply opType.tyClass.
     *
     *  Called only by Operation, to reduce the number of 
     *  left operand x right operand type combinations.
     *
     *  Error 219 is generated if the opType was invalid 
     *  for binary constant operations.
     *)
    BEGIN (* assert opType <> NIL *)
      IF class = subranges THEN opType := opType^.hostType;
      ELSIF class = doubles THEN opType := PointerTo(RR);
      ELSIF class = floats  THEN opType := PointerTo(RR);
      ELSIF class = cards THEN
        IF operand.intValue >= 0 THEN
          opType := PointerTo(ZZ);
        ELSE opType := PointerTo(UU);
        END;
      ELSIF class = ints THEN
        IF operand.intValue >= 0 THEN
          opType := PointerTo(ZZ);
        ELSE opType := PointerTo(II);
        END;
      ELSIF class = S1 THEN opType := PointerTo(chars);
      ELSE opType := NIL; Error(219);
      END;      
    END FixUp;

    PROCEDURE StringConcat (lClass : TyNodeClass;
			    rClass : TyNodeClass;
			VAR lValue : LexAttType;
			VAR rValue : LexAttType);
      VAR newHi,ix : CARDINAL;
    BEGIN
      MarkInterimSpellix();
      (* copy up to but not including nul char *)
      newHi := lValue.strHigh;
      IF lClass = S1 THEN 
	IF newHi <> 0 THEN  (* don't copy ""  (jl Mar 95) *)
	  CopyChar(lValue.charValue); 
        END;
      ELSE (* is SS *)
        FOR ix := lValue.stringIx TO lValue.stringIx + newHi - 1 DO
	  CopyChar(StringTable(ix));
	END;
      END;
      (* newHi is number of actual chars copied *)
      (* copy up to and also including nul char *)
      INC(newHi,rValue.strHigh);
      IF rClass = S1 THEN
	IF rValue.strHigh <> 0 THEN
	  CopyChar(rValue.charValue);
	END;
	CopyChar(""); 
      ELSE (* is SS *)
        FOR ix := rValue.stringIx TO rValue.stringIx + newHi DO
	  CopyChar(StringTable(ix));
	END;
      END;
      lValue.strHigh := newHi;
      lValue.stringIx := InterimSpellix();
      Commit();
    END StringConcat;

    PROCEDURE Operation(opr : TerminalSymbols;
                    VAR lTp : TypeDesc;
                        rTp : TypeDesc;
                    VAR lOp : LexAttType;
                        rOp : LexAttType);
    (*
     *  Perform the binary operation opr on constant left and right operands 
     *  with given types and values. The result replaces the left operand.
     *)
      VAR lClass, rClass : TyNodeClass;
	  tmp : LexAttType;
	  res : INTEGER;
          lo, hi, size, elem : CARDINAL;
	  fail,sign : BOOLEAN;

    BEGIN
      IF (lTp = NIL) OR (rTp = NIL) THEN lTp := NIL; RETURN END;  (* ##### *)
      lClass := lTp^.tyClass; 
      rClass := rTp^.tyClass;
      IF  (opr = plus) AND
	  ((lClass = S1) OR (lClass = SS)) AND
          ((rClass = S1) OR (rClass = SS)) THEN (* string concatenate *)
	StringConcat(lClass,rClass,lOp,rOp);
        lTp := PointerTo(SS); RETURN;				  (* ##### *)
      END;
      LOOP
        lClass := lTp^.tyClass; 
	rClass := rTp^.tyClass;
        IF lClass > chars THEN FixUp(lClass,lOp,lTp);
        ELSIF rClass > chars THEN FixUp(rClass,rOp,rTp);
        ELSE EXIT;
        END;
        IF (rTp = NIL) OR (lTp = NIL) THEN lTp := NIL; RETURN END; (* #### *)
      END;
      (* normal case first! *)
      IF (lClass <= UU) AND (rClass <= UU) THEN
       (*
	*  Notes on doing 33-bit arithmetic on a 32-bit machine.
	*
	*  Gardens Point Modula requires compile time arithmetic 
	*  to be done to 33 bit accuracy, so that meaningful 
	*  operations such as 90000000H + (-20000000H) can be
	*  performed.
	*
	*  The key concept is to do the arithmetic as unsigned 
	*  32-bit operations for multiplicative operators with
	*  a post check to see if a non-overflowing result can
	*  be mapped back into the MinInt .. MaxCard range.
	*
	*  For additive operators, the key is to do multi-word
	*  integer operations, with a 32-bit low significant 
	*  word and a one-bit (!) high significant word. 
	*
	*  However, for the moment, mixtures of II and UU are
	*  flagged with an error 220 by M2Traversal...
	*)
	IF lClass = II THEN Assert(rClass <> UU) END;
	IF rClass = II THEN Assert(lClass <> UU) END;
	sign := (lClass = II) OR (rClass = II);
        CASE opr OF
        | star  :
	    IF sign THEN
	      Safe.MulInt(lOp.intValue,rOp.intValue,res,fail);
	      IF fail AND ((rOp.intValue < 0) = (lOp.intValue < 0)) THEN
(* $T- *)	Safe.MulCrd(ABS(lOp.intValue),ABS(rOp.intValue),
						lOp.fixValue,fail);
(* $T= *)	lTp := PointerTo(UU);
	      ELSIF lOp.intValue < 0 THEN
			lTp := PointerTo(II) ELSE lTp := PointerTo(ZZ)
	      END;
	      lOp.intValue := res;  (* correct result even in UU case *)
	    ELSE
	      Safe.MulCrd(lOp.fixValue,rOp.fixValue,lOp.fixValue,fail);
	      IF lOp.fixValue > MAX(INTEGER) THEN
			lTp := PointerTo(UU) ELSE lTp := PointerTo(ZZ) END;
	    END;
	    IF fail THEN lTp := NIL; Error(215) END;
	| slash :
	    IF sign THEN
	      Safe.SlashI(lOp.intValue,rOp.intValue,lOp.intValue,fail);
	      IF lOp.intValue < 0 THEN
			lTp := PointerTo(II) ELSE lTp := PointerTo(ZZ) END;
	    ELSE
	      Safe.SlashC(lOp.fixValue,rOp.fixValue,lOp.fixValue,fail);
	      IF lOp.fixValue > MAX(INTEGER) THEN
			lTp := PointerTo(UU) ELSE lTp := PointerTo(ZZ) END;
	    END;
	    IF fail THEN lTp := NIL; Error(219) END;
	| remSy : 
	    IF sign THEN
	      Safe.RemInt(lOp.intValue,rOp.intValue,lOp.intValue,fail);
	      IF lOp.intValue < 0 THEN
			lTp := PointerTo(II) ELSE lTp := PointerTo(ZZ) END;
	    ELSE
	      Safe.RemCrd(lOp.fixValue,rOp.fixValue,lOp.fixValue,fail);
	      IF lOp.fixValue >  MAX(INTEGER) THEN
			lTp := PointerTo(UU) ELSE lTp := PointerTo(ZZ) END;
	    END;
	    IF fail THEN lTp := NIL; Error(219) END;
	| divSy  :
	    IF sign THEN
	      Safe.DivInt(lOp.intValue,rOp.intValue,lOp.intValue,fail);
	      IF lOp.intValue < 0 THEN
			lTp := PointerTo(II) ELSE lTp := PointerTo(ZZ) END;
	    ELSE
	      Safe.DivCrd(lOp.fixValue,rOp.fixValue,lOp.fixValue,fail);
	      IF lOp.fixValue > MAX(INTEGER) THEN
			lTp := PointerTo(UU) ELSE lTp := PointerTo(ZZ) END;
	    END;
	    IF fail THEN lTp := NIL; Error(219) END;
	| modSy  :
	    IF sign THEN
	      Safe.ModInt(lOp.intValue,rOp.intValue,lOp.intValue,fail);
	      lTp := PointerTo(ZZ);
	    ELSE
	      Safe.RemCrd(lOp.fixValue,rOp.fixValue,lOp.fixValue,fail);
	      IF lOp.fixValue > MAX(INTEGER) THEN
			lTp := PointerTo(UU) ELSE lTp := PointerTo(ZZ) END;
	    END;
	    IF fail THEN lTp := NIL; Error(219) END;
	| plus  :
	    IF sign THEN
	      Safe.AddInt(lOp.intValue,rOp.intValue,lOp.intValue,fail);
	      IF lOp.intValue < 0 THEN
			lTp := PointerTo(II) ELSE lTp := PointerTo(ZZ) END;
	    ELSE
	      Safe.AddCrd(lOp.fixValue,rOp.fixValue,lOp.fixValue,fail);
	      IF lOp.fixValue > MAX(INTEGER) THEN
			lTp := PointerTo(UU) ELSE lTp := PointerTo(ZZ) END;
	    END;
	    IF fail THEN lTp := NIL; Error(215) END;
	| minus :
	    IF sign THEN
	      Safe.SubInt(lOp.intValue,rOp.intValue,tmp.intValue,fail);
	      IF fail THEN
		Safe.SubCrd(lOp.fixValue,rOp.fixValue,tmp.fixValue,fail);
		lTp := PointerTo(UU);
	      ELSIF lOp.intValue < 0 THEN
			lTp := PointerTo(II) ELSE lTp := PointerTo(ZZ)
	      END;
	    ELSE
	      Safe.SubCrd(lOp.fixValue,rOp.fixValue,tmp.fixValue,fail);
	      IF fail THEN
		Safe.SubInt(lOp.intValue,rOp.intValue,tmp.intValue,fail);
		lTp := PointerTo(II);
	      ELSIF lOp.fixValue > MAX(INTEGER) THEN
			lTp := PointerTo(UU) ELSE lTp := PointerTo(ZZ)
	      END;
	    END;
	    lOp := tmp;
	    IF fail THEN lTp := NIL; Error(215) END;
        | equals, notEq :
            lOp.fixValue := ORD(OrdRelOp(opr,lTp,
                              ORD(lOp.fixValue),ORD(rOp.fixValue)));
            lTp := PointerTo(bools);
        | greater, grEqual : 
            IF lClass <> rClass THEN
              lOp.fixValue := ORD(ORD(lClass) > ORD(rClass));
            ELSE lOp.fixValue := ORD(OrdRelOp(opr,lTp,
                                   ORD(lOp.fixValue),ORD(rOp.fixValue)));
            END; 
            lTp := PointerTo(bools);
        | less, lessEq : 
            IF lClass <> rClass THEN
              lOp.fixValue := ORD(ORD(lClass) < ORD(rClass));
            ELSE lOp.fixValue := ORD(OrdRelOp(opr,lTp,
                                   ORD(lOp.fixValue),ORD(rOp.fixValue)));
            END; 
            lTp := PointerTo(bools);
	| andSy, orSy : lTp := NIL; Error(269);
        ELSE lTp := NIL; Error(219);
        END;
        RETURN;
      END;
      (* various special cases *)
      IF (rClass = chars) AND (lClass = chars) THEN
        lOp.fixValue := ORD(OrdRelOp(opr,lTp,
                          ORD(lOp.charValue),ORD(rOp.charValue)));
        lTp := PointerTo(bools);
      ELSIF (rClass = enums) AND (rTp = lTp) THEN
        lOp.fixValue := ORD(OrdRelOp(opr,lTp,
                          ORD(lOp.fixValue),ORD(rOp.fixValue)));
        lTp := PointerTo(bools);
      ELSIF rClass = sets THEN
        size := rTp^.size;
        IF (lClass = sets) AND (lTp = rTp) THEN
          CASE opr OF
            grEqual, equals, notEq, lessEq :
              lOp.fixValue := 
                ORD(SetRelop(size,opr,lOp.patternIx,rOp.patternIx));
              lTp := PointerTo(bools);
          | greater, less : Error(273);
          | plus,minus,star,slash :
              SetOperate(size,opr,lOp.patternIx,rOp.patternIx);
          ELSE Error(219);
          END;
        ELSIF (opr = inSy) AND (rTp^.baseType <> NIL) THEN
          WITH rTp^.baseType^ DO
            CASE tyClass OF
              subranges : lo := minRange; hi := maxRange;
            | enums     : lo := 0; hi := cardinality - 1;
            | chars     : lo := 0; hi := charMax;
            | bools     : lo := 0; hi := 1;
            END;
          END; (* now, is the element compatible? *)
	  rTp := rTp^.baseType;
	  IF rTp^.tyClass = subranges THEN rTp := rTp^.hostType END;
          IF Compatible(lTp,rTp) OR
		(rTp^.tyClass = cards) AND
		Compatible(lTp,PointerTo(ints)) THEN
            elem := OrdinalValue(lTp,lOp);
            IF (elem < lo) OR (elem > hi) THEN
              lOp.fixValue := ORD(FALSE);
            ELSE lOp.fixValue := ORD(SetInOp(elem,rOp.patternIx));
            END;
	    lTp := PointerTo(bools);				(* 17-Mar-92 *)
          ELSE Error(220); lTp := NIL;
          END;
        ELSE Error(219);
        END; (* if sets *)
      ELSIF (lClass = bools) AND (rClass = bools) THEN
        BoolOps(opr,lOp.fixValue,rOp.fixValue); (* lTp is OK *)
      ELSIF (lClass = RR) AND (rClass = RR) THEN
	FP_Overflow := FALSE;
        CASE opr OF
          star  : lOp.floatValue := lOp.floatValue * rOp.floatValue;
        | slash : IF rOp.floatValue = 0.0 THEN
		    IF lOp.floatValue < 0.0 THEN
		      lOp.floatValue := -INFINITY;
		    ELSE			(* 0.0 / 0.0 ?? *)
		      lOp.floatValue := INFINITY;
		    END;
		  ELSE		(* otherwise Alpha traps on this *)
		    lOp.floatValue := lOp.floatValue / rOp.floatValue;
		  END;
        | plus  : lOp.floatValue := lOp.floatValue + rOp.floatValue;
        | minus : lOp.floatValue := lOp.floatValue - rOp.floatValue;
        | equals : 
            lOp.fixValue := ORD(lOp.floatValue = rOp.floatValue);
            lTp := PointerTo(bools);
        | notEq : 
            lOp.fixValue := ORD(lOp.floatValue # rOp.floatValue);
            lTp := PointerTo(bools);
        | greater : 
            lOp.fixValue := ORD(lOp.floatValue > rOp.floatValue);
            lTp := PointerTo(bools);
        | grEqual : 
            lOp.fixValue := ORD(lOp.floatValue >= rOp.floatValue);
            lTp := PointerTo(bools);
        | less : 
            lOp.fixValue := ORD(lOp.floatValue < rOp.floatValue);
            lTp := PointerTo(bools);
        | lessEq : 
            lOp.fixValue := ORD(lOp.floatValue <= rOp.floatValue);
            lTp := PointerTo(bools);
        ELSE lTp := NIL; Error(219);
        END;
	IF lTp = rTp THEN (* result is RR *)
	  IF (lOp.floatValue = INFINITY) OR (lOp.floatValue = -INFINITY) THEN
	    Error(511);
	  ELSIF FP_Overflow THEN
	   (*
	    * Alpha produces rubbish for *,+,- overflows
	    * so use this flag and just generate +INFINITY
	    *)
	    lOp.floatValue := INFINITY;
	    Error(511);
	  END;
	END;
      ELSE lTp := NIL; Error(219);
      END;
    END Operation;

    PROCEDURE OrdRelOp(opr : TerminalSymbols;
                       oTp : TypeDesc;
                       lOp, rOp : CARDINAL) : BOOLEAN;
    (*
       Performs the operation on left and right operands.
       lOp and rOp must both be of ordinal type oTp.
       
       If the operation is not a relational operator, error 219 is generated 
       and FALSE returned.   
    *)
    BEGIN
      CASE opr OF
        equals : RETURN lOp = rOp;
      | notEq  : RETURN lOp # rOp;
      | greater : 
          IF IsSignedType(oTp) THEN
            RETURN CAST(INTEGER,lOp) > CAST(INTEGER,rOp);
          ELSE RETURN lOp > rOp;
          END; 
      | grEqual : 
          IF IsSignedType(oTp) THEN
            RETURN CAST(INTEGER,lOp) >= CAST(INTEGER,rOp);
          ELSE RETURN lOp >= rOp;
          END; 
      | less : 
          IF IsSignedType(oTp) THEN
            RETURN CAST(INTEGER,lOp) < CAST(INTEGER,rOp);
          ELSE RETURN lOp < rOp;
          END; 
      | lessEq : 
          IF IsSignedType(oTp) THEN
            RETURN CAST(INTEGER,lOp) <= CAST(INTEGER,rOp);
          ELSE RETURN lOp <= rOp;
          END; 
      ELSE Error(219); RETURN FALSE;
      END;
    END OrdRelOp;

(* ============================================================ *
 *  From here on the code for gp2d is different to take account *
 *  of possible cross-compilation configurations 		*
 *  =========================================================== *
 *  The important principle here is that constants are constr-  *
 *  ucted in the packing conventions of the TARGET MACHINE ...  *
 *  The constant in, is usually in the HOST MACHINE conventions *
 *  =========================================================== *
 *  Here there might need to be some care, if the target        *
 *  endian-ness is different to the host ...			*
 *  Also, the field might be incorrectly aligned for the host!  *
 *								*
 * 	Never make anything simple and efficient when a way	*
 * 	can be found to make it complex and wonderful.		*
 *								*
 *  =========================================================== *)

    PROCEDURE CopyConstant(con : LexAttType;
			   aTp : TypeDesc;
			   dTp : TypeDesc;
			   dst : ConBlock);
    (*
     *  this procedure packs components of constant contructors
     *  con is the lexical attribute value, typ the component type
     *  dst is a pointer to the constant at the point of insertion
     *
     *  Note that aTp is the _actual_ component -- could be SS
     *)
      VAR index, byte, card : CARDINAL;
	  fieldSize : CARDINAL;
          srcCon    : ConBlock;
	  srcSpx    : Spellix;
	  trick     : RECORD CASE : BOOLEAN OF
			| TRUE  : float : SHORTREAL;
			| FALSE : crdEl : CARDINAL;
		      END END;
    BEGIN
      IF (aTp = NIL) OR (dTp = NIL) OR (dst = NIL) THEN RETURN END;
      IF dTp^.tyClass = subranges THEN
	IF dTp^.size = dTp^.hostType^.size THEN dTp := dTp^.hostType;
	ELSIF dTp^.size = 1 THEN dTp := PointerTo(bytes);
	END;
      END;
      CASE dTp^.tyClass OF
      | pointers,adrs,hiddens : (* assert, can only be NIL == 0 *)
	  FOR index := 0 TO adrSize - 1 DO		(* jl Jun 94 *)
	    dst^[index] := 0C;
	  END;
(*
 *  pointers and proctypes not implemented here ...
 *
 *    | procTypes :				(* kjg Nov 92 *)
 *	  dst^[0] := con.bytes[0];		(* -coherent- *)
 *	  dst^[1] := con.bytes[1];
 *	  dst^[2] := con.bytes[2];
 *	  dst^[3] := con.bytes[3];
 *)
      | subranges, ints, cards, RR, doubles, floats :	(* jl Jun 94 *)
	  fieldSize := dTp^.size;
	  IF fieldSize < SIZE(WORD) THEN fieldSize := SIZE(WORD) END;
	  byte := (fieldSize - 1) * ORD(crossEndian);
	  IF dTp^.tyClass = floats THEN
	    trick.float := SFLOAT(con.floatValue); (* shorten *)
	    con.fixValue := trick.crdEl;	   (* this is little endian *)
	  ELSIF bigEndian THEN
	    IF crossEndian THEN byte := fieldSize - 1
	    ELSE		byte := fieldSize - dTp^.size
	    END;
	  END;
	  FOR index := 0 TO dTp^.size - 1 DO
	    dst^[index] := con.bytes[byte];
(* $T- *)   IF crossEndian THEN DEC(byte) ELSE INC(byte) END;  (* $T= *)
	  END;
      | records,arrays : 
	  IF (aTp^.tyClass = SS) OR
	     (aTp^.tyClass = S1) THEN
	    srcSpx := con.stringIx;
	    IF con.strHigh < dTp^.size THEN
	      card := con.strHigh;		(* include the nul *)
	    ELSE card := dTp^.size - 1;		(* copy full array *)
	    END;
	    FOR index := 0 TO card DO
	      dst^[index] := StringTable(srcSpx);
	      INC(srcSpx);
	    END;
	  ELSE (* usual case *)
	    srcCon := con.adrsValue;
(*
 *	    FOR index := 0 TO dTp^.size DO		!one too many!
 *)
	    FOR index := 0 TO dTp^.size - 1 DO		(* Oct 92 kjg *)
	      dst^[index] := srcCon^[index];
	    END;
	  END;
      | sets : (* variable, table[patternIx] *)
	  srcSpx := con.patternIx;
	  IF bigEndian = crossEndian THEN (* little endian *)
	    FOR index := 0 TO dTp^.size - 1 DO
	      dst^[index] := StringTable(srcSpx + index);
	    END;
	  ELSE						(* jl Jun 94 *)
	    index := 0;
	    WHILE index < dTp^.size DO
	      FOR byte := index + bytesInWord - 1 TO index BY -1 DO
	        dst^[byte] := StringTable(srcSpx); INC(srcSpx);
	      END;
	      INC(index,bytesInWord);
	    END;
	  END;
      | enums,bytes,bools : (* one byte, fixValue *)
	  dst^[0] := CHR(con.fixValue MOD 256);
      | chars : (* one byte, charValue *)
	  dst^[0] := con.charValue;
      | SS, S1, UU, ZZ, II, procTypes : Assert(FALSE);
      END; (* case *)
    END CopyConstant;

    PROCEDURE ExtractCon(VAR con : LexAttType; (* inout *)
			     typ : TypeDesc;
			     cmp : ConBlock);
      VAR i8          : Int8;
	  sign        : INTEGER;
	  fieldSize   : CARDINAL;
	  index, byte : CARDINAL;
	  trick       : RECORD CASE : BOOLEAN OF
			 | TRUE  : float : SHORTREAL;
			 | FALSE : crdEl : CARDINAL;
			END END;
    BEGIN
      IF typ = NIL THEN RETURN END;
      IF (typ^.tyClass = subranges) AND
	 (typ^.size = typ^.hostType^.size) THEN 
	typ := typ^.hostType;
      END;
      CASE typ^.tyClass OF
(*
 *    | procTypes :				(* kjg Nov 92 *)
 *	  con.bytes[0] := cmp^[0];		(* -coherent- *)
 *	  con.bytes[1] := cmp^[1];
 *	  con.bytes[2] := cmp^[2];
 *	  con.bytes[3] := cmp^[3];
 *)
						(* jl Jun 94 *)
      | II,ZZ,UU,subranges,cards,ints,RR,doubles,floats : 
	  fieldSize := typ^.size;
	  IF fieldSize < SIZE(WORD) THEN fieldSize := SIZE(WORD) END;
	  IF bigEndian AND (typ^.tyClass <> floats) THEN
	    byte := (typ^.size - 1) * ORD(NOT crossEndian);
	    FOR index := fieldSize - 1 TO fieldSize - typ^.size BY -1 DO
	      con.bytes[index] := cmp^[byte];
(* $T- *)     IF crossEndian THEN INC(byte) ELSE DEC(byte) END;  (* $T= *)
	    END;
	    FOR index := 1 TO fieldSize - typ^.size DO
	      con.bytes[index - 1] := 0C;
	    END;
	  ELSE
	    byte := (typ^.size - 1) * ORD(crossEndian);
	    FOR index := 0 TO typ^.size - 1 DO
	      con.bytes[index] := cmp^[byte];
(* $T- *)     IF crossEndian THEN DEC(byte) ELSE INC(byte) END;  (* $T= *)
	    END;
	    FOR index := typ^.size TO fieldSize - 1 DO
	      con.bytes[index] := 0C;
	    END;
	  END;
	  IF IsSignedType(typ) AND (fieldSize > typ^.size) THEN
	    IF bigEndian THEN
	      i8 := CAST(Int8,con.bytes[fieldSize - typ^.size]);
	    ELSE
	      i8 := CAST(Int8,con.bytes[typ^.size - 1]);
	    END;
	    sign := i8;	(* sign extend to host integer then clear sig. digits *)
	    sign := CAST(INTEGER,
		    CAST(BITSET,sign) - BITSET{0 .. typ^.size * 8 - 1});
	    INC(con.intValue,sign);  (* add in the sign bits *) 
	  ELSIF typ^.tyClass = floats THEN 
	    (* result will be packed into 32-bits *)
	    trick.crdEl := con.fixValue;
	    con.floatValue := FLOAT(trick.float);
	    (* now result is packed into 64-bits  *)
	  END;
      | records,arrays : 
	  con.adrsValue := cmp;
      | sets : (* variable, table[patternIx] *)
	  MarkInterimSpellix();
	  IF bigEndian = crossEndian THEN (* little endian *)
	    FOR index := 0 TO typ^.size - 1 DO
	      CopyChar(cmp^[index]);
	    END;
	  ELSE
	    index := 0;
	    WHILE index < typ^.size DO
	      FOR byte := index + bytesInWord - 1 TO index BY -1 DO
	        CopyChar(cmp^[byte]);
	      END;
	      INC(index,bytesInWord);
	    END;
	  END;
	  con.patternIx := InterimSpellix();
	  Commit();
      | enums,bytes,bools : (* one byte, fixValue *)
	  con.fixValue := ORD(cmp^[0]);
      | chars,S1 : (* one byte, charValue *)
	  con.charValue := cmp^[0];
      | pointers,adrs,hiddens : (* assert, can only be NIL == 0 *)
	  con.adrsValue := NIL;
      ELSE Assert(FALSE);
      END; (* case *)
    END ExtractCon;

END M2CompOperations.
