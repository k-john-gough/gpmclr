(****************************************************************)
(*                                                              *)
(*                 Modula-2 Compiler Source Module              *)
(*                                                              *)
(*                     Runtime literal chain                    *)
(*                                                              *)
(*     (c) copyright 1988 Faculty of Information Technology     *)
(*                                                              *)
(*      original module : kjg November 1988                     *)
(*      modifications   : kjg 10-Nov-89 now handles other cons  *)
(*			: kjg 30-Nov-89 hash tables for lits    *)
(*			: kjg 24-Feb-90 fix for bug where bad   *)
(*				offset alignment was entered	*)
(*			: kjg 12-Jun-90 changes to treatment of *)
(*				charNums (compat to S1s)	*)
(*			: kjg 14-Oct-90 align sets for 68k ver. *)
(*			: kjg 23-Oct-91 reals go on lit chain   *)
(*								*)
(*   =============== merged mips and i386 source ============	*)
(*			   kjg 22 Mar 93			*)
(*								*)
(****************************************************************
$Log: m2litcha.mod,v $
Revision 1.3  1994/07/15 04:12:43  lederman
check for 0.0 and just flag the rtOffset

# Revision 1.2  1994/07/01  04:40:24  lederman
# fix RealHash so (a) table is initialised with a NaN for both big & small
# endian and (b) it doesn't do a fp compare against the NaaaN
#
# Revision 1.1  1994/04/07  04:59:04  lederman
# Initial revision
#
*****************************************************************
Revision 1.2  93/08/05  11:33:29  gough
turn off overflow checks during hash processing for real hash
*****************************************************************)

IMPLEMENTATION MODULE M2LitChain;
(*
 *   IMPORT StdError;
 *)
IMPORT SYSTEM;
FROM Types IMPORT Card32;
FROM M2Designators IMPORT ExprDesc, ExprRec, ExprNodeClass;
FROM M2MachineConstants IMPORT bytesInWord, bigEndian;
FROM M2NameHandler IMPORT StringTable;
FROM M2TabInitialize IMPORT PointerTo;
FROM M2Alphabets IMPORT Spellix, LexAttType;
FROM M2NodeDefs IMPORT 
      TypeDesc, TypeRec, TyNodeClass, TyClassSet;

(*
  -- exported variables --
  VAR chainHead : ExprDesc; (* head of chain to dump *)
      chainTail : ExprDesc; (* tail of chain to dump *)
*)
  VAR   nextFree : CARDINAL;  (* next free byte index *)
  CONST constructs = TyClassSet{sets,records,arrays,RR}; (* RRs added Oct 91 *)
        stringTabs = TyClassSet{sets,SS};

  (* =============================================== *)

  MODULE SpixHash;
    IMPORT Spellix;
    EXPORT QUALIFIED Seek, Enter;

    (*
     *  Notes on changes of 12-Jun-90
     *  charNums have S1 type, with stringIx = 0. They
     *  are not in the string table but are constructed
     *  as required by during constant data output in
     *  the output module. This fact requires some
     *  special case code in seek and enter here.
     *)

    CONST size = 41;

    VAR Table : ARRAY [0 .. size - 1] OF
		  RECORD
		    spx : Spellix;
		    off : CARDINAL;
		  END;

    PROCEDURE  Seek(spix   : Spellix;
		VAR offset : CARDINAL;
		VAR found  : BOOLEAN);
      VAR hash : CARDINAL;
    BEGIN
      hash := spix MOD size;
      IF Table[hash].spx = spix THEN
	found := (spix <> 0); 		(* so charNums never found *)
        offset := Table[hash].off;
      ELSE found := FALSE;
      END;
    END Seek;

    PROCEDURE Enter(spix  : Spellix;
		    offset : CARDINAL);
    BEGIN
      IF spix = 0 THEN RETURN END;
      WITH Table[spix MOD size] DO
        spx := spix; off := offset;
      END;
    END Enter;

    VAR ix : CARDINAL;

  BEGIN
    FOR ix := 0 TO size - 1 DO
      Table[ix].spx := 0;
    END;
  END SpixHash;
      
  (* =============================================== *)

  MODULE HeapHash;
    IMPORT SYSTEM;
    EXPORT QUALIFIED Seek, Enter;

    CONST size = 41;

    VAR Table : ARRAY [0 .. size - 1] OF
		  RECORD
		    spx : SYSTEM.ADDRESS;
		    off : CARDINAL;
		  END;

    PROCEDURE  Seek(adrs   : SYSTEM.ADDRESS;
		VAR offset : CARDINAL;
		VAR found  : BOOLEAN);
      VAR hash : CARDINAL;
    BEGIN
      hash := SYSTEM.CAST(CARDINAL,adrs) MOD size;
      IF Table[hash].spx = adrs THEN
	found := TRUE; 
        offset := Table[hash].off;
      ELSE found := FALSE;
      END;
    END Seek;

    PROCEDURE Enter(adrs   : SYSTEM.ADDRESS;
		    offset : CARDINAL);
    BEGIN
      WITH Table[SYSTEM.CAST(CARDINAL,adrs) MOD size] DO
        spx := adrs; off := offset;
      END;
    END Enter;

    VAR ix : CARDINAL;

  BEGIN
    FOR ix := 0 TO size - 1 DO
      Table[ix].spx := NIL;
    END;
  END HeapHash;

  (* =============================================== *)

(* $T-  overflows must be turned off for hash computations *)
  MODULE RealHash;
    IMPORT SYSTEM, Card32, bigEndian;
    EXPORT QUALIFIED Seek, Enter;

    CONST size = 41;

    TYPE RealUnion =  RECORD CASE : BOOLEAN OF
			| TRUE  : fp : REAL;
			| FALSE : lo,hi : Card32;
		      END END;

    VAR Table : ARRAY [0 .. size - 1] OF
		  RECORD
		    dbl : RealUnion;
		    off : CARDINAL;
		  END;

    PROCEDURE  Seek(real   : REAL;
		VAR offset : CARDINAL;
		VAR found  : BOOLEAN);
      VAR hash : CARDINAL;
	  dmmy : RealUnion;
    BEGIN
      dmmy.fp := real;
      hash := (dmmy.hi + dmmy.lo) MOD size;
      WITH Table[hash] DO	(* don't rely on fp compares against NaN's *)
	IF (dbl.lo = dmmy.lo) AND (dbl.hi = dmmy.hi) THEN 
	  found := TRUE;
          offset := off;
	ELSE found := FALSE;
	END;
      END;
    END Seek;

    PROCEDURE Enter(real   : REAL;
		    offset : CARDINAL);
      VAR dmmy : RealUnion;
    BEGIN
      dmmy.fp := real;
      WITH Table[(dmmy.hi + dmmy.lo) MOD size] DO
        dbl.fp := real; off := offset;
      END;
    END Enter;

    VAR ix : CARDINAL;

  BEGIN
    IF bigEndian THEN			(* jl Jun 94 *)
      FOR ix := 0 TO size - 1 DO
        Table[ix].dbl.lo := 0FFF00000H;	(* NaN *)
        Table[ix].dbl.hi := 1;
      END;
    ELSE
      FOR ix := 0 TO size - 1 DO
        Table[ix].dbl.hi := 0FFF00000H;
        Table[ix].dbl.lo := 1;
      END;
    END;
  END RealHash;
(* $T=  overflows must be turned off for hash computations *)
      
  (* =============================================== *)

  PROCEDURE FixLiteral(VAR lit : ExprDesc);
    VAR class : TyNodeClass;
        step  : CARDINAL;
        mask  : CARDINAL;
	litTyp : TypeDesc;
	litVal : LexAttType;
	oldOffset : CARDINAL;
        isOld, isSpix : BOOLEAN;
  BEGIN
    IF lit^.exprClass = selConstNode THEN (* a selected constant *)
      litTyp := lit^.name.variable^.conType;
      litVal := lit^.name.variable^.conValue;
    ELSE (* an ordinary literal *)
      litTyp := lit^.exprType;
      litVal := lit^.conValue;
    END;
    class  := litTyp^.tyClass;
    IF NOT (class IN constructs) AND (class <> SS) THEN RETURN END;
(*
 *    here, avoid duplication of literals by checking if
 *    an rtOffset is already allocated for this spelling-index,
 *    or real value or heap address as the case may be.
 *)
    isSpix := class IN stringTabs;
    IF isSpix THEN 
      SpixHash.Seek(litVal.patternIx,oldOffset,isOld);
    ELSIF class = RR THEN
      IF litVal.floatValue = 0.0 THEN
	oldOffset := literalZero;			(* jl Jun 94 *)
	isOld := TRUE;				(* 0.0 => pshZ; iToD *)
      ELSE
        RealHash.Seek(litVal.floatValue,oldOffset,isOld);
      END;
    ELSE 
      HeapHash.Seek(litVal.adrsValue,oldOffset,isOld);
    END;
    IF isOld THEN 
      (*
       *  no need to link, the old literal is on chain already
       *  specifically, the nextFree must not be changed by
       *  moving to a new alignment boundary until it is known
       *  that the literal _will_ actually be entered (kjg feb 90)
       *)
      lit^.rtOffset := oldOffset; 
      (* ==> nextFree is not changed *)
    ELSE (* ok to adjust nextFree *)
       (*
	*  for all versions, irrespective of the alignment in memory
	*  generally, sets are quad-aligned in global const data area
	*		... now word aligned (jl Jun 94 )
	*)
      IF class = sets THEN (* round up to alignment boundary *)
        nextFree := SYSTEM.CAST(CARDINAL,
			SYSTEM.CAST(BITSET,nextFree + bytesInWord - 1) - 
			SYSTEM.CAST(BITSET,bytesInWord - 1));
        step := litTyp^.size;
      ELSIF class <> SS THEN (* round up to alignment boundary *)
        mask := ORD(litTyp^.alignMask);
        nextFree := SYSTEM.CAST(CARDINAL,
			SYSTEM.CAST(BITSET,nextFree + mask) - 
			SYSTEM.CAST(BITSET,mask));
        step := litTyp^.size;
      ELSE (* class = SS *)
(* this could be unnecessary with the new changes ... *)
        step := litVal.strHigh + 1;
        (* strHigh also 1 for "", so adjust *)
        IF  (step = 2) AND
	    (litVal.stringIx <> 0) AND			(* new 12-Jun-90 *)
            (StringTable(litVal.stringIx) = 0C) THEN
          step := 1;
        END;
      END;
      IF isSpix THEN 
        SpixHash.Enter(litVal.patternIx,nextFree);
      ELSIF class = RR THEN
        RealHash.Enter(litVal.floatValue,nextFree);
	step := 12;					(* jl Jun 94 *)
      ELSE 
        HeapHash.Enter(litVal.adrsValue,nextFree);
      END;
      lit^.rtOffset := nextFree;
      INC(nextFree,step);
      (*
        now link this literal to chain
      *)
      IF chainHead = NIL THEN chainHead := lit;
      ELSE chainTail^.chainLnk := lit;
      END;
      lit^.chainLnk := NIL;
      chainTail := lit;
    END;
  END FixLiteral;

  PROCEDURE ConstDataSize() : CARDINAL;
  (* returns the constant data array in target machine words    *)
  BEGIN
    RETURN (nextFree + bytesInWord - 1) DIV bytesInWord;
  END ConstDataSize;

BEGIN
  nextFree := 0;
  chainHead := NIL;
  chainTail := NIL;
END M2LitChain.
