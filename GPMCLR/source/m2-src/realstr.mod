
IMPLEMENTATION MODULE RealStr;
(*
 * Purpose:
 *   Provides REAL/string conversions
 *
 * Log:
 *   April 96  jl  initial version
 *
 * Notes:
 *   Complies with ISO/IEC 10514-1:1996  (as RealStr)
 *
 *)
  FROM ConvTypes IMPORT ScanClass, ScanState;
  FROM RealConv  IMPORT ScanReal;
  FROM DtoA      IMPORT dtoa, strtod, errno, ERANGE;
  FROM Storage   IMPORT ALLOCATE, DEALLOCATE;
  FROM Types     IMPORT Int32;


(***************************************************************)
(*                                                             *)
(*                   PRIVATE - NOT EXPORTED                    *)
(*                                                             *)
(***************************************************************)

  TYPE
     CHAR_star = POINTER TO ARRAY [0 .. MAX(CARDINAL)] OF CHAR;

 (*
  * Append a trailing null if necessary before going awol to C
  *)
  PROCEDURE StrToD(VAR (* IN *) str : ARRAY OF CHAR) : REAL;
    VAR real : REAL;
	p    : CHAR_star;
	ix   : CARDINAL;
  BEGIN 
    IF LENGTH(str) > HIGH(str) THEN  (* no trailing null *)
      ALLOCATE(p, HIGH(str) + 2);
      FOR ix := 0 TO HIGH(str) DO p^[ix] := str[ix] END;
      p^[HIGH(str) + 1] := "";
      real := strtod(p^);
      DEALLOCATE(p, HIGH(str) + 2);
      RETURN real;
    END;
    RETURN strtod(str);
  END StrToD;

  (*===============================================================*)

  PROCEDURE SetOverflow(VAR (* OUT *) str : ARRAY OF CHAR; neg : BOOLEAN);

    CONST infinity = "+INFINITY";

    VAR tmp   : ARRAY [0 .. LENGTH(infinity)] OF CHAR;
	index : CARDINAL;
  BEGIN
    tmp := infinity;
    index := 0;
    WHILE (index <= LENGTH(infinity)) AND (index <= HIGH(str)) DO
      str[index] := tmp[index]; INC(index);
    END;
    IF neg THEN str[0] := "-" END;
  END SetOverflow;

  (*===============================================================*)

  PROCEDURE ExpLen(exp : CARDINAL) : CARDINAL;
  BEGIN
    IF    exp = 0   THEN RETURN 0;
    ELSIF exp < 10  THEN RETURN 3;
    ELSIF exp < 100 THEN RETURN 4;
    ELSE RETURN 5;
    END;
  END ExpLen;

  (*===============================================================*)

  PROCEDURE  CopyCh(ch : CHAR;
		VAR ix : CARDINAL;
		VAR st : ARRAY OF CHAR);
  BEGIN
    IF ix <= HIGH(st) THEN st[ix] := ch; INC(ix) END;
  END CopyCh;

  (*===============================================================*)

  PROCEDURE CopyExp(ex : INTEGER;
		VAR ix : CARDINAL;
		VAR st : ARRAY OF CHAR);
    VAR abX, val : CARDINAL;
  BEGIN
    CopyCh("E",ix,st);
    IF ex > 0 THEN CopyCh("+",ix,st) ELSE CopyCh("-",ix,st) END;
    abX := ABS(ex); val := abX;
    IF abX >= 100 THEN 
      CopyCh(CHR(val DIV 100 + ORD("0")),ix,st);
      val := val MOD 100;
    END;
    IF abX >= 10 THEN 
      CopyCh(CHR(val DIV 10 + ORD("0")),ix,st);
    END;
    CopyCh(CHR(val MOD 10 + ORD("0")),ix,st);
  END CopyExp;


(***************************************************************)
(*                                                             *)
(*                     PUBLIC - EXPORTED                       *)
(*                                                             *)
(***************************************************************)

 (*
  * Ignores any leading spaces in str. If the subsequent characters in str are in
  * the format of a signed real number, assigns a corresponding value to real.
  * Assigns a value indicating the format of str to res.
  *)
  PROCEDURE StrToReal (str: ARRAY OF CHAR; VAR real: REAL; VAR res: ConvResults);
    VAR  class : ScanClass;
	 state : ScanState;
         ix    : CARDINAL;
  BEGIN
    class := padding;
    state := ScanReal;
    FOR ix := 0 TO HIGH(str) DO
      IF (class = padding) AND (str[ix] = "") THEN res := strEmpty; RETURN END;
      state(str[ix], class, state);
      CASE class OF
      | invalid :
	  res := strWrongFormat; RETURN;
      | terminator :
	  IF str[ix] <> "" THEN res := strWrongFormat; RETURN END;
	  real := StrToD(str);
	  IF errno = ERANGE THEN res := strOutOfRange; RETURN END;
	  res := strAllRight; RETURN;
      ELSE (* continue *)
      END;
    END;
    (* We get here if str does not include the trailing "" *)
    IF class = padding THEN res := strEmpty;       RETURN END;
    state("", class, state);
    IF class = invalid THEN res := strWrongFormat; RETURN END;
    real := StrToD(str);
    IF errno = ERANGE  THEN res := strOutOfRange;  RETURN END;
    res := strAllRight;
  END StrToReal;

  (*===============================================================*)

 (*
  * Converts the value of real to floating-point string form, with sigFigs
  * significant digits, and copies the possibly truncated result to str.
  *)
  PROCEDURE RealToFloat (real: REAL; sigFigs: CARDINAL; VAR str: ARRAY OF CHAR);
    VAR len, fWid, index, ix : CARDINAL;
        dExp   : Int32; (* decimal exponent *)
	neg    : BOOLEAN;
	digits : CHAR_star;
  BEGIN
    IF sigFigs = 0 THEN sigFigs := 16  END; (* default *)

    digits := dtoa(real,2,sigFigs,dExp,neg);
    IF dExp = 9999 THEN SetOverflow(str, neg); RETURN END;

    DEC(dExp);  (* move decimal point one place right *)
    index := 0;
    IF neg THEN CopyCh("-",index,str) END;
    fWid := LENGTH(digits^);
    IF fWid = 0 THEN  (* result is 0 *)
      CopyCh("0",index,str);
      dExp := 0;
    ELSE
      CopyCh(digits^[0],index,str);
    END;
    IF sigFigs > 1 THEN 
      CopyCh(".",index,str);
      IF fWid > 1 THEN
	FOR ix := 1  TO fWid - 1    DO CopyCh(digits^[ix],index,str) END;
      END;
      FOR ix := fWid TO sigFigs - 1 DO CopyCh("0",index,str) END;
    END;
    IF dExp <> 0 THEN CopyExp(dExp,index,str) END;
    IF index <= HIGH(str) THEN str[index] := "" END;
  END RealToFloat;

  (*===============================================================*)

 (*
  * Converts the value of real to floating-point string form, with sigFigs
  * significant digits, and copies the possibly truncated result to str.
  * The number is scaled with one to three digits in the whole number part and
  * with an exponent that is a multiple of three.
  *)
  PROCEDURE RealToEng (real: REAL; sigFigs: CARDINAL; VAR str: ARRAY OF CHAR);
    VAR len, index, ix : CARDINAL;
        dExp   : Int32; (* decimal exponent *)
	fact   : [0 .. 3];
	neg    : BOOLEAN;
	digits : CHAR_star;
  BEGIN
    IF sigFigs = 0 THEN sigFigs := 16 END; (* default *)

    digits := dtoa(real,2,sigFigs,dExp,neg);
    IF dExp = 9999 THEN SetOverflow(str, neg); RETURN END;

    len := LENGTH(digits^);
    IF len = 0 THEN dExp := 1 END;  (* result = 0 *)
    fact := ((dExp - 1) MOD 3) + 1;
    DEC(dExp,fact);	(* make exponent multiple of three *)

    index := 0;
    IF neg THEN CopyCh("-",index,str) END;
    IF fact <= len THEN
      FOR ix := 0   TO fact - 1 DO CopyCh(digits^[ix],index,str) END;
    ELSE
      IF len > 0 THEN
	FOR ix := 0 TO len  - 1 DO CopyCh(digits^[ix],index,str) END;
      END;
      FOR ix := len TO fact - 1 DO CopyCh("0",index,str) END;
    END;
    IF fact < sigFigs THEN 
      CopyCh(".",index,str);
      IF fact < len THEN
	FOR ix := fact TO len - 1 DO CopyCh(digits^[ix],index,str) END;
      ELSE
	len := fact;
      END;
      FOR ix := len TO sigFigs - 1 DO CopyCh("0",index,str) END;
    END;
    IF dExp <> 0 THEN CopyExp(dExp,index,str) END;
    IF index <= HIGH(str) THEN str[index] := "" END;
  END RealToEng;

  (*===============================================================*)

 (*
  * Converts the value of real to fixed-point string form, rounded to the given
  * place relative to the decimal point, and copies the result to str.
  *)
  PROCEDURE RealToFixed (real: REAL; place: INTEGER; VAR str: ARRAY OF CHAR);
    VAR lWid, fWid, len, index, ix : CARDINAL;
        dExp   : Int32;
        neg    : BOOLEAN;
	digits : CHAR_star;
  BEGIN
  (* the decimal point and fraction part *)
    IF place >= 0 THEN fWid := place + 1 ELSE fWid := 0; INC(place); END;

    digits := dtoa(real,3,place,dExp,neg);
    IF dExp = 9999 THEN SetOverflow(str, neg); RETURN END;

    len := LENGTH(digits^);
    IF len = 0 THEN dExp := 1 END; (* result is 0 *)
    IF dExp > 0 THEN lWid := dExp END;

    index := 0;
    IF neg THEN CopyCh("-",index,str) END;
    IF dExp <= 0 THEN CopyCh("0",index,str);
    ELSE
      IF lWid <= len THEN
	FOR ix := 0   TO lWid - 1 DO CopyCh(digits^[ix],index,str) END;
      ELSE
	IF len > 0 THEN
	  FOR ix := 0 TO len - 1  DO CopyCh(digits^[ix],index,str) END;
	END;
	FOR ix := len TO lWid - 1 DO CopyCh("0",index,str) END;
      END;
    END;
    IF fWid > 0 THEN 
      CopyCh(".",index,str);
      DEC(fWid);
      IF dExp <= 0 THEN
	FOR ix := 1 TO ORD(-dExp) DO CopyCh("0",index,str) END;
	FOR ix := 0 TO len - 1    DO CopyCh(digits^[ix],index,str) END;
	DEC(fWid,ORD(-dExp) + len);
      ELSIF lWid < len THEN
	FOR ix := lWid TO len - 1 DO CopyCh(digits^[ix],index,str) END;
	DEC(fWid,len - lWid);
      END;
      FOR ix := 1 TO fWid DO CopyCh("0",index,str) END;
    END;
    IF index <= HIGH(str) THEN str[index] := "" END;
  END RealToFixed;

  (*===============================================================*)

 (*
  * Converts the value of real as RealToFixed if the sign and magnitude can be
  * shown within the capacity of str, or otherwise as RealToFloat, and copies
  * the possibly truncated result to str.
  * The number of places or significant digits are implementation-defined.
  *)
  PROCEDURE RealToStr (real: REAL; VAR str: ARRAY OF CHAR);
    VAR lWid, index : CARDINAL;
        dExp   : Int32;
        neg    : BOOLEAN;
	digits : CHAR_star;
  BEGIN
   (* Estimate the exponent by converting to float to fill string
    * leaving room for sign and ".". This should work in most cases.
    * (Denormals for one stuff up ...)
    *)
    digits := dtoa(real,2,INT(HIGH(str)) - INT(real < 0.0),dExp,neg);
    IF dExp = 9999 THEN SetOverflow(str, neg); RETURN END;

    lWid := ORD(neg);
    IF digits^[0] # 0C THEN
      IF dExp > 0 THEN INC(lWid,dExp - 1);
      ELSE  (* denormals will print as 0.00... *)
	IF dExp < -308 THEN lWid := 0 ELSE INC(lWid,2 - dExp) END;
      END;
    END;

   (* Allow trailing "." to be elided if exponent > 0 i.e. place = -1 *)
    IF lWid <= HIGH(str) THEN
      IF dExp > 0 THEN
	RealToFixed(real,INT(HIGH(str) - lWid) - 1,str);    (* -n.ppp *)
      ELSE
	RealToFixed(real,(HIGH(str) - ORD(neg) - 1),str);   (* -0.ppp *)
      END;
    ELSE			     (* use RealToFloat - sigFigs > 0 *)
      lWid := ORD(neg) + ExpLen(ABS(dExp - 1));
      IF lWid >= HIGH(str) THEN   (* truncated result *)
	RealToFloat(real,1,str);
      ELSE
	RealToFloat(real,HIGH(str) - lWid,str);
      END;
    END;
  END RealToStr;


END RealStr.
