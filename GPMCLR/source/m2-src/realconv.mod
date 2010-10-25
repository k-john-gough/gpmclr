(****************************************************************
$Log: realconv.mod,v $
Revision 1.1  1996/09/06 07:51:22  lederman
Initial revision

*)

IMPLEMENTATION MODULE RealConv;
(*
 * Purpose:
 *   Provides low-level REAL/string conversions
 *
 * Log:
 *   April 96  jl  initial version
 *
 * Notes:
 *   Complies with ISO/IEC 10514-1:1996 
 *
 *)

  FROM ConvTypes IMPORT ScanClass, ScanState;
  FROM RealStr   IMPORT StrToReal, RealToFloat, RealToEng, RealToFixed;
  FROM ProgArgs  IMPORT Assert;

(***************************************************************)
(*                                                             *)
(*                   PRIVATE - NOT EXPORTED                    *)
(*                                                             *)
(***************************************************************)

  TYPE 
    CharSet = SET OF CHAR;

  CONST
    digits = CharSet{"0","1","2","3","4","5","6","7","8","9"};
    signs  = CharSet{"+","-"};
    space  = CharSet{1C .. " "};

  TYPE
    RealConvException = (NoException, NotRealNumber);

  VAR 
    currRealConvException : RealConvException;


  PROCEDURE RAISERealConvException(x : RealConvException; s : ARRAY OF CHAR);
  VAR
    errMsg : ARRAY [0 .. 29] OF CHAR;
    str    : ARRAY [0 .. 99] OF CHAR;
    ix,ls  : CARDINAL;
  BEGIN
    currRealConvException := x;
    errMsg := " : Not a REAL number";
    ls := LENGTH(s);
    IF ls > 0 THEN
      FOR ix := 0 TO ls - 1 DO str[ix] := s[ix] END;
    END;
    FOR ix := 0 TO LENGTH(errMsg) DO str[ix + ls] := errMsg[ix] END;

    Assert(FALSE, str);

  END RAISERealConvException;


(***************************************************************)
(*                                                             *)
(*                     PUBLIC - EXPORTED                       *)
(*                                                             *)
(***************************************************************)


 (*
  * Represents the start state of a finite state scanner for real numbers - assigns
  * class of inputCh to chClass and a procedure representing the next state to
  * nextState.
  *)
  PROCEDURE ScanReal (inputCh  : CHAR; 
		  VAR chClass  : ScanClass;
                  VAR nextState: ScanState);
  BEGIN
    IF inputCh IN digits THEN
      nextState := Scan2; chClass := valid;
    ELSIF inputCh IN signs THEN
      nextState := Scan1; chClass := valid;
    ELSE
      nextState := ScanReal;
      IF inputCh IN space THEN chClass := padding ELSE chClass := invalid END;
    END;
  END ScanReal;

  PROCEDURE Scan1(inputCh      : CHAR;		(* RS *)
                  VAR chClass  : ScanClass;
                  VAR nextState: ScanState);
  BEGIN
    IF inputCh IN digits THEN
      nextState := Scan2; chClass := valid;
    ELSE
      nextState := Scan1; chClass := invalid;
    END;
  END Scan1;

  PROCEDURE Scan2(inputCh      : CHAR;		(* P *)
                  VAR chClass  : ScanClass;
                  VAR nextState: ScanState);
  BEGIN
    IF inputCh IN digits THEN
      nextState := Scan2; chClass := valid;
    ELSIF inputCh = "." THEN 
      nextState := Scan3; chClass := valid;
    ELSIF CAP(inputCh) = "E" THEN
      nextState := Scan4; chClass := valid;
    ELSE
      chClass := terminator;
    END;
  END Scan2;

  PROCEDURE Scan3(inputCh      : CHAR;		(* F *)
                  VAR chClass  : ScanClass;
                  VAR nextState: ScanState);
  BEGIN
    IF inputCh IN digits THEN
      nextState := Scan3; chClass := valid;
    ELSIF CAP(inputCh) = "E" THEN
      nextState := Scan4; chClass := valid;
    ELSE
      chClass := terminator;
    END;
  END Scan3;

  PROCEDURE Scan4(inputCh      : CHAR;		(* E *)
                  VAR chClass  : ScanClass;
                  VAR nextState: ScanState);
  BEGIN
    IF inputCh IN digits THEN
      nextState := Scan6; chClass := valid;
    ELSIF inputCh IN signs THEN
      nextState := Scan5; chClass := valid;
    ELSE
      nextState := Scan4; chClass := invalid;
    END;
  END Scan4;

  PROCEDURE Scan5(inputCh      : CHAR;		(* SE *)
                  VAR chClass  : ScanClass;
                  VAR nextState: ScanState);
  BEGIN
    IF inputCh IN digits THEN
      nextState := Scan6; chClass := valid;
    ELSE
      nextState := Scan5; chClass := invalid;
    END;
  END Scan5;

  PROCEDURE Scan6(inputCh      : CHAR;		(* WE *)
                  VAR chClass  : ScanClass;
                  VAR nextState: ScanState);
  BEGIN
    IF inputCh IN digits THEN
      nextState := Scan6; chClass := valid;
    ELSE
      chClass := terminator;
    END;
  END Scan6;

  (*===============================================================*)

 (*
  * Returns the format of the string value for conversion to REAL.
  *)
  PROCEDURE FormatReal (str: ARRAY OF CHAR): ConvResults;
    VAR res  : ConvResults;
	real : REAL;
  BEGIN
    StrToReal(str,real,res);
    RETURN res;
  END FormatReal;

  (*===============================================================*)

 (*
  * Returns the value corresponding to the real number string value str
  * if str is well-formed; otherwise raises the RealConv exception.
  *)
  PROCEDURE ValueReal (str: ARRAY OF CHAR): REAL;
    VAR res  : ConvResults;
	real : REAL;
  BEGIN
    StrToReal(str,real,res);
    IF res <> strAllRight THEN
      RAISERealConvException(NotRealNumber,"ValueReal");
    END;
    currRealConvException := NoException;
    RETURN real;
  END ValueReal;

  (*===============================================================*)

 (*
  * Returns the number of characters in the floating-point string representation
  * of real with sigFigs significant figures.
  *)
  PROCEDURE LengthFloatReal (real: REAL; sigFigs: CARDINAL): CARDINAL;
    VAR tmp : ARRAY [0 .. 127] OF CHAR;
  BEGIN
    IF sigFigs > 100 THEN 	(* some arbitrarily large limit *)
      RealToFloat(real,100,tmp);
      RETURN LENGTH(tmp) + sigFigs - 100; (* add trailing zeros *)
    END;
    RealToFloat(real,sigFigs,tmp);
    RETURN LENGTH(tmp);
  END LengthFloatReal;

  (*===============================================================*)

 (*
  * Returns the number of characters in the floating-point engineering string
  * representation of real with sigFigs significant figures.
  *)
  PROCEDURE LengthEngReal (real: REAL; sigFigs: CARDINAL): CARDINAL;
    VAR tmp : ARRAY [0 .. 127] OF CHAR;
  BEGIN
    IF sigFigs > 100 THEN 	(* some arbitrarily large limit *)
      RealToEng(real,100,tmp);
      RETURN LENGTH(tmp) + sigFigs - 100; (* add trailing zeros *)
    END;
    RealToEng(real,sigFigs,tmp);
    RETURN LENGTH(tmp);
  END LengthEngReal;

  (*===============================================================*)

 (*
  * Returns the number of characters in the fixed-point string representation of
  * real rounded to the given place relative to the decimal point.
  *)
  PROCEDURE LengthFixedReal (real: REAL; place: INTEGER): CARDINAL;
    VAR tmp : ARRAY [0 .. 410] OF CHAR;  (* can have up to 309 digits before '.' *)
  BEGIN
    IF place > 100 THEN 	(* some arbitrarily large limit *)
      RealToFixed(real,100,tmp);
      RETURN LENGTH(tmp) + place - 100;   (* add trailing zeros *)
    END;
    RealToFixed(real,place,tmp);
    RETURN LENGTH(tmp);
  END LengthFixedReal;

  (*===============================================================*)

 (*
  * Returns TRUE if the current coroutine is in the exceptional execution state
  * because of the raising of an exception in a routine from this module;
  * otherwise returns FALSE.
  *)
  PROCEDURE IsRConvException (): BOOLEAN;
  BEGIN
    (* IF in exceptional execution state *)
    RETURN currRealConvException <> NoException;
  END IsRConvException;

BEGIN	(* Module initialisation *)
  currRealConvException := NoException;
END RealConv.
