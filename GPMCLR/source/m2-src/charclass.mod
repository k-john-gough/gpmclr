(****************************************************************
$Log: charclass.mod,v $
Revision 1.1  1996/09/06 07:51:13  lederman
Initial revision

*)

IMPLEMENTATION MODULE CharClass;
(*
 * Purpose:
 *   Classification of values of the type CHAR
 *
 * Log:
 *   5/09/96  JL  Initial Release
 *
 * Notes:
 *   Complies with ISO/IEC 10514-1:1996
 *)

TYPE CharSet = SET OF CHAR;

(* Returns TRUE if and only if ch is classified as a numeric character *)
PROCEDURE IsNumeric (ch: CHAR): BOOLEAN;
BEGIN
  RETURN ch IN CharSet{'0' .. '9'};
END IsNumeric;


(* Returns TRUE if and only if ch is classified as a letter *)
PROCEDURE IsLetter (ch: CHAR): BOOLEAN;
BEGIN
  RETURN ch IN CharSet{'a' .. 'z', 'A' .. 'Z'};
END IsLetter;


(* Returns TRUE if and only if ch is classified as an upper case letter *)
PROCEDURE IsUpper (ch: CHAR): BOOLEAN;
BEGIN
  RETURN ch IN CharSet{'A' .. 'Z'};
END IsUpper;


(* Returns TRUE if and only if ch is classified as a lower case letter *)
PROCEDURE IsLower (ch: CHAR): BOOLEAN;
BEGIN
  RETURN ch IN CharSet{'a' .. 'z'};
END IsLower;


(* Returns TRUE if and only if ch represents a control function *)
PROCEDURE IsControl (ch: CHAR): BOOLEAN;
BEGIN
  RETURN (ch < " ");
END IsControl;


(* Returns TRUE if and only if ch represents a space character or 
   a format effector *)
PROCEDURE IsWhiteSpace (ch: CHAR): BOOLEAN;
BEGIN
  RETURN ch IN CharSet{1C .. ' '};
END IsWhiteSpace;

END CharClass.
