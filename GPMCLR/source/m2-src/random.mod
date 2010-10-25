
(****************************************************************)
(*                                                              *)
(*         Gardens Point Modula-2 Library Implementation        *)
(*                                                              *)
(*                                                              *)
(*     (c) Copyright 1996 Faculty of Information Technology     *)
(*              Queensland University of Technology             *)
(*                                                              *)
(*     Permission is granted to use, copy and change this       *)
(*     program as long as the copyright message is left intact  *)
(*                                                              *)
(****************************************************************
$Log: random.mod,v $
Revision 1.1  1996/09/06 07:49:19  lederman
Initial revision

*)

IMPLEMENTATION MODULE Random;
(*
 * Random number generator.
 * Uses the 'Minimal standard random number generator' described by
 * Park & Miller, CACM 31,10,Oct 88 p1192. The code has been checked
 * for the 10001st random as specified in Park & Miller p1195.
 *
 * This version returns a REAL randomly distributed in the closed range
 * [0.0,1.0], and will be correct if the real mantissa is 46 bits
 * or larger (including sign bit). The sequence is guaranteed to produce
 * all values of the form n/m for n = 0 to m, where m is 2147483646
 * (=2**31-2), before cycling.
 *)

FROM ProgArgs IMPORT UNIXtime;

CONST
  a = 16807.0;
  m = 2147483647.0;
VAR
  temp : REAL;
  current : REAL;

PROCEDURE InitRandom (seed : REAL);
(* Initialise the random number generator with the given seed.		*)
(* The seed should be in the range [1.0,2147483646.0] - values outside	*)
(* this range are clamped to the extreme values.			*)
(* If InitRandom is not called, the system clock is used to initialise	*)
(* the sequence; thus InitRandom must be called to create a		*)
(* reproducible sequence.						*)
(* InitRandom may be called as often as needed.				*)
BEGIN
  IF seed < 1.0 THEN seed := 1.0; END;
  IF seed > m-1.0 THEN seed := m-1.0; END;
  current := seed;
END InitRandom;

PROCEDURE Random() : REAL;
(* Return the next pseudo-random number in the closed range [0.0,1.0]	*)
BEGIN
  temp := a * current;
  current := temp - m * FLOAT(TRUNC(temp/m));
  (* Variation from Park & Miller: shift 1..(m-1) to 0..(m-2), then
     divide by (m-2) to give closed range *)
  RETURN (current-1.0) / (m-2.0);
END Random; 

BEGIN
  temp := FLOAT(UNIXtime());
  current := temp - m * FLOAT(TRUNC(temp/m));
END Random.
