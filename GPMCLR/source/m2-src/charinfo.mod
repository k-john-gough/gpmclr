
(*  ***********************************************************************
    *                                                                     *
    *               Modula-2 CharInfo Libary Implementation               *
    *                                                                     *
    *       (c) copyright  1988 Faculty of Information Technology         *
    *                                                                     *
    *           Original module : kjg                                     *
    *             modifications : pms  9 Feb 93 - merged platform         *
    *                                             specific files          *
    *                             pms 04-Mar-93 - removed machine.cpp.    *
    *                                             Specific code obtained  *
    *                                             from cc switches in     *
    *                                             COMPILEcsrc             *
    *                                                                     *
    ***********************************************************************
*)
IMPLEMENTATION MODULE CharInfo;
FROM Ascii IMPORT lf;

(* *************** CharInfo_IsEOL () *************** *)
PROCEDURE IsEOL(ch : CHAR) : BOOLEAN;
BEGIN
  RETURN (ch = lf);
END IsEOL;

(* *************** CharInfo_IsDigit () *************** *)
PROCEDURE IsDigit(ch : CHAR) : BOOLEAN;
BEGIN
  RETURN ((ch >= "0") AND (ch <= "9"));
END IsDigit;

(* *************** CharInfo_IsDigit () *************** *)
PROCEDURE IsSpace(ch : CHAR) : BOOLEAN;
BEGIN
  RETURN ((ch <> 0C) AND (ch <= " "));
END IsSpace;

(* *************** CharInfo_IsSign () *************** *)
PROCEDURE IsSign(ch : CHAR) : BOOLEAN;
BEGIN
  RETURN ((ch = "-") OR (ch = "+"));
END IsSign;

(* *************** CharInfo_IsLetter () *************** *)
PROCEDURE IsLetter(ch : CHAR) : BOOLEAN;
BEGIN
  RETURN (((ch >= "a") AND (ch <= "z")) OR ((ch >= "A") AND (ch <= "Z")));
END IsLetter;

(* *************** CharInfo_IsUpper () *************** *)
PROCEDURE IsUpper(ch : CHAR) : BOOLEAN;
BEGIN
  RETURN ((ch >= "A") AND (ch <= "Z"));
END IsUpper;

(* *************** CharInfo_IsLower () *************** *)
PROCEDURE IsLower(ch : CHAR) : BOOLEAN;
BEGIN
  RETURN ((ch >= "a") AND (ch <= "z"));
END IsLower;

(* *************** CharInfo_IsControl () *************** *)
PROCEDURE IsControl(ch : CHAR) : BOOLEAN;
BEGIN
  RETURN (ch < " ");
END IsControl;

(* *************** CharInfo_EOL () *************** *)
PROCEDURE EOL() : CHAR;
BEGIN
  RETURN lf;
END EOL;

END CharInfo.
