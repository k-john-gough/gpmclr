(****************************************************************)
(*                                                              *)
(*         Gardens Point Modula-2 Library Implementation        *)
(*                                                              *)
(*	   Safe arithmetic operations for compile-time  	*)
(*                                                              *)
(*     (c) Copyright 1996 Faculty of Information Technology     *)
(*              Queensland University of Technology             *)
(*                                                              *)
(*     Permission is granted to use, copy and change this       *)
(*     program as long as the copyright message is left intact  *)
(*                                                              *)
(****************************************************************
$Log: safe.mod,v $
Revision 1.1  1996/09/06 07:49:21  lederman
Initial revision

*)

(* ============================================================ *
 * original module kjg June 1994 
 * ============================================================ *)

IMPLEMENTATION MODULE Safe;

  (* In all cases, the semantics are as follows *)
  (* -return the correct result, or fail = TRUE *)

(* $T- *) (* $R- *)

  PROCEDURE AbsInt(lSrc      : INTEGER; 
		    VAR dst  : INTEGER; 
		    VAR fail : BOOLEAN);
  BEGIN
    fail := lSrc = MIN(INTEGER);
    IF lSrc < 0 THEN dst := -lSrc ELSE dst := lSrc END;
  END AbsInt;

  PROCEDURE NegInt(lSrc      : INTEGER; 
		    VAR dst  : INTEGER; 
		    VAR fail : BOOLEAN);
  BEGIN
    fail := lSrc = MIN(INTEGER);
    dst := -lSrc;
  END NegInt;

  PROCEDURE AddInt(lSrc,rSrc : INTEGER; 
		    VAR dst  : INTEGER; 
		    VAR fail : BOOLEAN);
  BEGIN
    dst := lSrc + rSrc;
    fail := (lSrc < 0) AND (rSrc < 0) AND (dst >= 0) OR
	    (lSrc > 0) AND (rSrc > 0) AND (dst <= 0);
  END AddInt;

  PROCEDURE AddCrd(lSrc,rSrc : CARDINAL; 
		    VAR dst  : CARDINAL; 
		    VAR fail : BOOLEAN);
  BEGIN
    dst := lSrc + rSrc;
    fail := (rSrc > dst) OR (lSrc > dst);
  END AddCrd;

  PROCEDURE SubInt(lSrc,rSrc : INTEGER; 
		    VAR dst  : INTEGER; 
		    VAR fail : BOOLEAN);
  BEGIN
    dst := lSrc - rSrc;
    fail := (lSrc < 0)  AND (rSrc > 0) AND (dst >= 0) OR
	    (lSrc >= 0) AND (rSrc < 0) AND (dst <= 0);
  END SubInt;


  PROCEDURE SubCrd(lSrc,rSrc : CARDINAL; 
		    VAR dst  : CARDINAL; 
		    VAR fail : BOOLEAN);
  BEGIN
    dst := lSrc - rSrc;
    fail := lSrc < rSrc;
  END SubCrd;


  PROCEDURE DivInt(lSrc,rSrc : INTEGER;  (* Modula2 DIV *)
		    VAR dst  : INTEGER;  (* 2 quadrants *)
		    VAR fail : BOOLEAN);
  BEGIN
    fail := (rSrc <= 0);
    IF NOT fail THEN dst := lSrc DIV rSrc END;
  END DivInt;


  PROCEDURE DivInt4Q(lop,rop : INTEGER;  (* Modula3 DIV *)
		    VAR dst  : INTEGER;  (* 4 quadrants *)
		    VAR fail : BOOLEAN);
  BEGIN
   (*
    *  This code relies implicitly on the assumption that
    *  the Modula2 implementation, with range testing off
    *  will generate the correct four quadrant behaviour.
    *  This is true for native code backends, at least...
    *)
    fail := (rop = 0) OR (lop = MIN(INTEGER)) AND (rop = -1);
    IF NOT fail THEN dst := lop DIV rop END;
  END DivInt4Q;

  PROCEDURE DivCrd(lSrc,rSrc : CARDINAL; 
		    VAR dst  : CARDINAL; 
		    VAR fail : BOOLEAN);
  BEGIN
    fail := rSrc = 0;
    IF NOT fail THEN dst := lSrc DIV rSrc END;
  END DivCrd;

  PROCEDURE SlashI(lSrc,rSrc : INTEGER; 
		    VAR dst  : INTEGER; 
		    VAR fail : BOOLEAN);
  BEGIN
    fail := (rSrc = 0) OR (lSrc = MIN(INTEGER)) AND (rSrc = -1);
    IF NOT fail THEN dst := lSrc / rSrc END;
  END SlashI;

  PROCEDURE SlashC(lSrc,rSrc : CARDINAL; 
		    VAR dst  : CARDINAL; 
		    VAR fail : BOOLEAN);
  BEGIN
    fail := rSrc = 0;
    IF NOT fail THEN dst := lSrc / rSrc END;
  END SlashC;

  PROCEDURE RemInt(lSrc,rSrc : INTEGER; 
		    VAR dst  : INTEGER; 
		    VAR fail : BOOLEAN);
  BEGIN
    fail := (rSrc = 0) OR (lSrc = MIN(INTEGER)) AND (rSrc = -1);
    IF NOT fail THEN dst := lSrc REM rSrc END;
  END RemInt;

  PROCEDURE RemCrd(lSrc,rSrc : CARDINAL; 
		    VAR dst  : CARDINAL; 
		    VAR fail : BOOLEAN);
  BEGIN
    fail := rSrc = 0;
    IF NOT fail THEN dst := lSrc REM rSrc END;
  END RemCrd;

  PROCEDURE ModInt(lSrc,rSrc : INTEGER;  (* Modula2 MOD *)
		    VAR dst  : INTEGER;  (* 2 quadrants *)
		    VAR fail : BOOLEAN);
  BEGIN
    fail := rSrc <= 0;
    IF NOT fail THEN dst := lSrc MOD rSrc END;
  END ModInt;

  PROCEDURE ModInt4Q(lop,rop : INTEGER;  (* Modula3 MOD *)
		    VAR dst  : INTEGER;  (* 4 quadrants *)
		    VAR fail : BOOLEAN);
  BEGIN
   (*
    *  This code relies implicitly on the assumption that
    *  the Modula2 implementation, with range testing off
    *  will generate the correct four quadrant behaviour.
    *  This is true for native code backends, at least...
    *)
    fail := (rop = 0) OR (lop = MIN(INTEGER)) AND (rop = -1);
    IF NOT fail THEN dst := lop MOD rop END;
  END ModInt4Q;

  PROCEDURE ModCrd(lSrc,rSrc : CARDINAL; 
		    VAR dst  : CARDINAL; 
		    VAR fail : BOOLEAN);
  BEGIN
    fail := rSrc = 0;
    IF NOT fail THEN dst := lSrc MOD rSrc END;
  END ModCrd;

  PROCEDURE MulInt(lSrc,rSrc : INTEGER; 
		    VAR dst  : INTEGER; 
		    VAR fail : BOOLEAN);
  BEGIN
    dst := lSrc * rSrc;
    fail := (lSrc = MIN(INTEGER)) AND (rSrc = -1) OR
	    (rSrc <> 0) AND (dst / rSrc <> lSrc);
  END MulInt;

  PROCEDURE MulCrd(lSrc,rSrc : CARDINAL; 
		    VAR dst  : CARDINAL; 
		    VAR fail : BOOLEAN);
  BEGIN
    dst := lSrc * rSrc;
    fail := (rSrc <> 0) AND (dst DIV rSrc <> lSrc);
  END MulCrd;

END Safe.
