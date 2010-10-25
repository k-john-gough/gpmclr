
IMPLEMENTATION MODULE WholeStr;
(*
 * Purpose:
 *   Whole-number/string conversions
 *
 * Log:
 *   April 96  jl  initial version
 *
 * Notes:
 *   Complies with ISO/IEC 10514-1:1996
 *
 *)


 (*
  * Ignores any leading spaces in str. If the subsequent characters in str are in the
  * format of a signed whole number, assigns a corresponding value to int. Assigns a
  * value indicating the format of str to res.
  *)
  PROCEDURE StrToInt(str: ARRAY OF CHAR; VAR int: INTEGER; VAR res: ConvResults);
    CONST
      limit = MAX(INTEGER) DIV 10;

    VAR ix    : CARDINAL;
	total : CARDINAL;
	max   : CARDINAL;
	neg   : BOOLEAN;
        state : [0 .. 2];
  BEGIN
    total := 0; 
    state := 0; 
    neg   := FALSE;
    max   := MAX(INTEGER);
    FOR ix := 0 TO HIGH(str) DO
      CASE str[ix] OF
      | 0C : (* string termination *)
          IF    state = 0   THEN res := strEmpty;
          ELSIF state = 1   THEN res := strWrongFormat;
	  ELSIF total > max THEN res := strOutOfRange;
	    IF neg THEN int := MIN(INTEGER) ELSE int := MAX(INTEGER) END;
	  ELSE                   res := strAllRight;			(*$T-*)
	    IF neg THEN int := -INT(total)  ELSE int := INT(total) END; (*$T=*)
	  END;
	  RETURN;
      | 1C .. " " : (* white space *)
          IF state <> 0 THEN res := strWrongFormat; RETURN END; (* else skip *)
      | "+", "-" :
          IF state <> 0 THEN res := strWrongFormat; RETURN;
          ELSE
	    state := 1;
	    IF str[ix] = "-" THEN INC(max); neg := TRUE END;
          END;
      | "0" .. "9" : (* decimal digits *)
          IF total = 0 THEN (* first digit *)
            total := ORD(str[ix]) - ORD("0"); state := 2;
          ELSIF total > limit THEN 
	    res := strOutOfRange;
	    IF neg THEN int := MIN(INTEGER) ELSE int := MAX(INTEGER) END;
	    RETURN;
          ELSE
	    total := total * 10 + (ORD(str[ix]) - ORD("0"));
          END;
      ELSE res := strWrongFormat; RETURN;
      END;
    END;
    IF    state = 0   THEN res := strEmpty;
    ELSIF state = 1   THEN res := strWrongFormat;
    ELSIF total > max THEN res := strOutOfRange;
      IF neg THEN int := MIN(INTEGER) ELSE int := MAX(INTEGER) END;
    ELSE                   res := strAllRight;			  (*$T-*)
      IF neg THEN int := -INT(total)  ELSE int := INT(total) END; (*$T=*)
    END;
  END StrToInt;

 (*===============================================================*)

 (*
  * Converts the value of int to string form and copies the possibly truncated
  * result to str.
  *)
  PROCEDURE IntToStr(int: INTEGER; VAR str: ARRAY OF CHAR);
    VAR arg, len, val, ix, index : CARDINAL;
  BEGIN
    IF int = MIN(INTEGER) THEN
      arg := MAX(INTEGER) + 1;
    ELSE
      arg := ABS(int);
    END;
    IF int < 0 THEN str[0] := "-"; ix := 1 ELSE ix := 0 END;
    len := ix;
    val := arg;
    WHILE val > 9 DO val := val DIV 10; INC(len) END;
    IF len < HIGH(str) THEN str[len+1] := 0C END;
    FOR index := len TO ix BY -1 DO
      IF index <= HIGH(str) THEN
        str[index] := CHR(arg MOD 10 + ORD("0"));
      END;
      arg := arg DIV 10;
    END;
  END IntToStr;

 (*===============================================================*)

 (*
  * Ignores any leading spaces in str. If the subsequent characters in str are in
  * the format of an unsigned whole number, assigns a corresponding value to card.
  * Assigns a value indicating the format of str to res.
  *)
  PROCEDURE StrToCard(str: ARRAY OF CHAR; VAR card: CARDINAL; VAR res: ConvResults);
    CONST
      limit = MAX(CARDINAL) DIV 10;

    VAR ix    : CARDINAL;
	total : CARDINAL;
        empty : BOOLEAN;
  BEGIN
    total := 0;
    empty := TRUE;
    FOR ix := 0 TO HIGH(str) DO
      CASE str[ix] OF
      | 0C : (* string termination *)
          IF empty THEN res := strEmpty;
	  ELSE		res := strAllRight; card := total;
	  END;
	  RETURN;
      | 1C .. " " : (* white space *)
          IF NOT empty THEN res := strWrongFormat; RETURN END; (* else skip *)
      | "0" .. "9" : (* decimal digits *)
          IF total = 0 THEN (* first digit *)
            total := ORD(str[ix]) - ORD("0"); empty := FALSE;
          ELSIF (total > limit) OR ((total = limit) AND (str[ix] > "5")) THEN
	    res  := strOutOfRange;	(* correct for 32-bit & 64-bit !! *)
	    card := MAX(CARDINAL);
	    RETURN;
          ELSE
	    total := total * 10 + (ORD(str[ix]) - ORD("0"));
          END;
      ELSE res := strWrongFormat; RETURN;
      END;
    END;
    IF empty THEN res := strEmpty;
    ELSE	  res := strAllRight; card := total;
    END;
  END StrToCard;

 (*===============================================================*)

 (*
  * Converts the value of card to string form and copies the possibly truncated
  * result to str.
  *)
  PROCEDURE CardToStr(card: CARDINAL; VAR str: ARRAY OF CHAR);
    VAR len, val, index : CARDINAL;
  BEGIN
    val := card;
    len := 0;
    WHILE val > 9 DO val := val DIV 10; INC(len) END;
    IF len < HIGH(str) THEN str[len+1] := 0C END;
    FOR index := len TO 0 BY -1 DO
      IF index <= HIGH(str) THEN
        str[index] := CHR(card MOD 10 + ORD("0"));
      END;
      card := card DIV 10;
    END;
  END CardToStr;

END WholeStr.

