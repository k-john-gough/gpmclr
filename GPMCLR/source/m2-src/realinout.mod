
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
(* first version : kjg December 1991 (from RealStr)		*)
(* modification record ---------------------------------------- *)
(*                                                              *)
(*  pms  8 Jul 94  : ReadReal no longer loops endlessly at EOF  *)
(*  pms 27 Oct 94  : Replaces RealInOut.c on Unix platforms     *)
(*  pms 19 Jun 95  : Customised IsNaNS code for both endianness *) 
(*  jl  April 96   : Rewritten using RealStr and dtoa libraries	*)
(*								*)
(****************************************************************
$Log: realinout.mod,v $
Revision 1.1  1996/09/06 07:49:20  lederman
Initial revision

*)

IMPLEMENTATION MODULE RealInOut;

  IMPORT InOut, RealStr, RealConv;
  FROM Types        IMPORT Int32;
  FROM RealStr      IMPORT ConvResults;
  FROM ConvTypes    IMPORT ScanClass, ScanState;
  FROM DtoA         IMPORT dtoa;

  TYPE
     CHAR_star = POINTER TO ARRAY [0 .. MAX(CARDINAL)] OF CHAR;

  (*===============================================================*)

  PROCEDURE ReadReal(VAR real : REAL);
    TYPE
      chCnt = [0 .. 500];	(* arbitrary limit *)

    VAR class : ScanClass;
	state : ScanState;
	ch    : CHAR;
	res   : ConvResults;
	str   : ARRAY chCnt OF CHAR;
	index : chCnt;
  BEGIN
    Done := FALSE;
    index := 0;
    class := padding;
    state := RealConv.ScanReal;
    InOut.Read(ch);	(* Skip leading space *)
    state(ch, class, state);
    WHILE InOut.Done AND (class = padding) DO
      InOut.Read(ch);
      state(ch, class, state);
    END;
    IF InOut.Done THEN
      WHILE InOut.Done AND (class = valid) AND (index < MAX(chCnt)) DO
	str[index] := ch; INC(index);
        InOut.Read(ch);
	IF NOT InOut.Done THEN ch := 0C END;
	state(ch, class, state);
      END;
      IF class = terminator THEN
	str[index] := 0C;
	RealStr.StrToReal(str, real, res);
        Done := (res = strAllRight) OR (res = strOutOfRange);
      END;
    END;
  END ReadReal;

  (*===============================================================*)

  PROCEDURE WriteReal(real : REAL; width : CARDINAL);
    CONST
      Inf = "INFINITY";

    VAR string : ARRAY [0 .. 31] OF CHAR;
	ix     : CARDINAL;
	sig,len: CARDINAL;
	places : INTEGER;
        dExp   : Int32; (* decimal exponent *)
	neg    : BOOLEAN;
	digits : CHAR_star;
  BEGIN
    digits := dtoa(real,0,0,dExp,neg);
    IF dExp = 9999 THEN				(* overflow *)
      IF width > LENGTH(Inf) + 1 THEN
        FOR ix := 2 TO width - LENGTH(Inf) DO InOut.Write(" ") END;
      END;
      IF neg THEN InOut.Write("-") ELSE InOut.Write("+") END;
      InOut.WriteString(Inf);
    ELSE
      sig := LENGTH(digits^);
      IF (dExp < 0) OR (dExp > 7) THEN		(* use Float format *)
	IF sig > 7 THEN sig := 7 END;		(* max 7 sig. digits *)
	IF sig < 2 THEN sig := 2 END;		(* '.0' on single digits *)
(*
	len := RealConv.LengthFloatReal(real,sig);
	IF len > width THEN
	  IF len - width >= sig THEN sig := 1 ELSE DEC(sig,len - width) END;
	END;
*)
	RealStr.RealToFloat(real,sig,string);
      ELSE					(* use Fixed format *)
	IF sig > 8 THEN sig := 8 END;		(* max 8 sig. digits *)
	places := INT(sig) - dExp;
	IF places <= 0 THEN places := -1 END;	(* supress trailing '.' *)
(*
	len := RealConv.LengthFixedReal(real,places);
	IF len > width THEN
	  DEC(places,len - width);
	  IF places <= 0 THEN places := -1 END;
	END;
*)
	RealStr.RealToFixed(real,places,string);
      END;
      len := LENGTH(string);
      IF len < width THEN
        FOR ix := 1 TO width - len DO InOut.Write(" ") END;
      END;
      InOut.WriteString(string);
    END;
  END WriteReal;

END RealInOut.
