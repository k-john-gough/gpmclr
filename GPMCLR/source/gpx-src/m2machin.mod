(****************************************************************)
(*								*)
(*		Modula-2 Compiler Source Module			*)
(*								*)
(*             Definition of Machine Constants                  *)
(*								*)
(*     (c) copyright 1988 Faculty of Information Technology     *)
(*								*)
(*      original module : kjg March 1988                        *)
(*      modifications   : kjg March 1993 version detects endian *) 
(*			: kjg March 1993 new config inlineTests *)
(*								*)
(****************************************************************
$Log: m2machin.mod,v $
Revision 1.16  1997/01/16 03:59:41  gough
        initialize new variables optDensity, defDensity.

Revision 1.15  1996/11/27 02:01:58  lederman
add exceptOK keyword

Revision 1.14  1996/07/29 23:58:51  gough
initialize the oP5 value

Revision 1.13  1995/10/18 00:45:34  lederman
added initialisation of INFINITY

Revision 1.12  1995/10/10 23:26:04  lederman
gdbStabX parsing added

# Revision 1.11  1995/03/17  02:56:24  lederman
# Change to Version 3 -- requires matching changes in BUILD2
#
# Revision 1.10  1995/01/06  03:35:37  gough
#  remove export of jumpTabElSize
#
# Revision 1.9  1994/11/15  04:30:36  gough
#  put in gdb support keyed on config tag "gdbStabs"
#
# Revision 1.8  1994/10/11  07:15:36  gough
# refRecords and sunValueStructs are now compatible
#
# Revision 1.7  1994/10/10  06:06:00  gough
# more specific error messages from bad config files
#
# Revision 1.6  1994/10/10  05:12:07  gough
# install new Boolean sunStructs with .cfg flag sunValueStructs
#
# Revision 1.5  1994/09/19  07:12:51  lederman
# allow jumpTabElSize to be smaller than wordSize
#
# Revision 1.4  1994/09/19  04:21:32  lederman
# set versionNumber back to 2 and hang the consequences...
#
# Revision 1.3  1994/07/15  03:23:14  lederman
# change versionNumber = 3 ==> 64-bit host
#
# Revision 1.2  1994/07/01  05:09:51  lederman
# add handling for wordSize64;  removed obsoleted noTestExpand
#
# Revision 1.1  1994/04/07  05:00:38  lederman
# Initial revision
*****************************************************************)

IMPLEMENTATION MODULE M2MachineConstants;
  IMPORT SYSTEM;
  FROM ProgArgs      IMPORT Assert;
  FROM Types         IMPORT Card32;
  FROM M2InOut       IMPORT OpenConfigFile, DiagName;
  FROM M2NameHandler IMPORT EnterString, retCutBkt;
  FROM M2Alphabets   IMPORT HashBucketType, TerminalSymbols, LexAttType;
  FROM M2Scanner     IMPORT InitScanner, GetSymbol, symbol, lexAtt;

  VAR maxFieldAlignHb,
      maxParamAlignHb,
      minParamAlignHb,
      fixParamHb,
      stkParamHb,
      interfaceHb,
      stackMarkSizeHb,
      jumpTabElSizeHb,
      displayElSizeHb,
      stackInvertedHb,
      stackUprightHb,
      inlineTestsHb,
      refRecordsHb,
      bigEndianHb,
      externRecRetPtrHb,
      externArrRetPtrHb,
      sunValueStructsHb,
      calleeCutPars,
      wordSize64,
      exceptFlag,
      gdbFlag, gdbXFlag,
      littleEndianHb : HashBucketType;
      
(* ============================================================== *
 *  TYPE  AlignMap = ARRAY [1 .. 8] OF CHAR;
 *
 *  VAR   alignMap : AlignMap;  (* this is the TARGET align map *)
 *
 *   (* this is the HOST endian attribute *)
 *    CONST bigEndian   = TRUE;  (* this implies that chars pack  *)
 *                        (* so that "abcd" is packed with "a" in *)
 *                        (* the most significant end of the word *)
 *                        (* FALSE ==> littleEndian like VAX etc. *)
 *                        (* TRUE  ==> bigEndian like M68k etc.   *)
 *
 *    VAR   crossEndian : BOOLEAN; 
 *    (* ==> host and target are different *)
 *
 *    VAR   stackInverted : BOOLEAN;
 *    (* ==> stack grows downward in address space *)
 *
 *    VAR   parsFixed   : BOOLEAN;
 *
 * ============================================================== *)

  VAR   parModeSet : BOOLEAN;
  CONST bad = "bad gp2d.cfg: ";

  PROCEDURE InitMachineVariables();
    VAR maxFA : CARDINAL;
	minPA : CARDINAL;
	maxPA : CARDINAL;
	index : CARDINAL;

    PROCEDURE ParseCommand;
      VAR idBkt : HashBucketType;
    BEGIN
      IF lexAtt.hashIx = maxFieldAlignHb THEN
        GetSymbol;
        Assert(symbol=equals,bad + "expected '='"); GetSymbol;
        Assert(symbol=fixNum,bad + "expected max-field number"); 
        maxFA := lexAtt.fixValue;
      ELSIF lexAtt.hashIx = stackMarkSizeHb THEN
        GetSymbol;
        Assert(symbol=equals,bad + "expected '='"); GetSymbol;
        Assert(symbol=fixNum,bad + "expected mark-size number"); 
        stackMarkSize := lexAtt.intValue;
      ELSIF lexAtt.hashIx = displayElSizeHb THEN
        GetSymbol;
        Assert(symbol=equals,bad + "expected '='"); GetSymbol;
        Assert(symbol=fixNum,bad + "expected disp-elSize number"); 
        displayElSize := lexAtt.fixValue;
      ELSIF lexAtt.hashIx = jumpTabElSizeHb THEN
        GetSymbol;
        Assert(symbol=equals,bad + "expected '='"); GetSymbol;
        Assert(symbol=fixNum,bad + "expected disp-elSize number"); 
      ELSIF lexAtt.hashIx = interfaceHb THEN
        GetSymbol;
        Assert((symbol = ident) AND
	   (lexAtt.hashIx <> minParamAlignHb),
	   bad + "expected 'minParamAlign'");
        GetSymbol;
        Assert(symbol=equals,bad + "expected '='"); GetSymbol;
        Assert(symbol=fixNum,bad + "expected min-param number"); 
      ELSIF lexAtt.hashIx = minParamAlignHb THEN
        GetSymbol;
        Assert(symbol=equals,bad + "expected '='"); GetSymbol;
        Assert(symbol=fixNum,bad + "expected min-param number"); 
	minPA := lexAtt.fixValue;
      ELSIF lexAtt.hashIx = maxParamAlignHb THEN
        GetSymbol;
        Assert(symbol=equals,bad + "expected '='"); GetSymbol;
        Assert(symbol=fixNum,bad + "expected max-param number"); 
	maxPA := lexAtt.fixValue;
      ELSIF lexAtt.hashIx = fixParamHb THEN
        Assert(NOT parModeSet,bad + "param mode set twice");
        parModeSet := TRUE;
	parsFixed := TRUE;
      ELSIF lexAtt.hashIx = stkParamHb THEN
        Assert(NOT parModeSet,bad + "param mode set twice");
        parModeSet := TRUE;
        parsFixed := FALSE;
      ELSIF lexAtt.hashIx = stackInvertedHb THEN
         stackInverted := TRUE;
      ELSIF lexAtt.hashIx = stackUprightHb THEN
         stackInverted := FALSE;
      ELSIF lexAtt.hashIx = bigEndianHb THEN
        crossEndian := NOT bigEndian;
      ELSIF lexAtt.hashIx = littleEndianHb THEN
        crossEndian := bigEndian;
      ELSIF lexAtt.hashIx = inlineTestsHb THEN
        expandTests := TRUE;
      ELSIF lexAtt.hashIx = refRecordsHb THEN
        refRecords := TRUE;
      ELSIF lexAtt.hashIx = externRecRetPtrHb THEN
        extRecRetPtr := TRUE;
      ELSIF lexAtt.hashIx = externArrRetPtrHb THEN
        extArrRetPtr := TRUE;
      ELSIF lexAtt.hashIx = sunValueStructsHb THEN
        sunStructs := TRUE;
	Assert(refRecords,bad + "sunValueStructs needs refRecords first");
      ELSIF lexAtt.hashIx = gdbFlag THEN
	gdbSupport := TRUE;
      ELSIF lexAtt.hashIx = gdbXFlag THEN
	gdbSupport := TRUE;
	gdbXCOFF   := TRUE;
      ELSIF lexAtt.hashIx = exceptFlag THEN
	exceptOK := TRUE;
      ELSIF lexAtt.hashIx = wordSize64 THEN
	Assert(SIZE(SYSTEM.WORD) = 8,
		bad + "wordSize64 only valid on 64-bit host");
	bitsInWord  := 64;
	bytesInWord := 8;
	intMax      := MAX(INTEGER);	(* 64-bit mods jl - June 94 *)
	cardMax     := MAX(CARDINAL);
	adrSize     := 8;
      ELSE 
	idBkt := lexAtt.hashIx;
        GetSymbol;
	IF symbol <> equals THEN 
	  Assert(FALSE,bad + "bad config command");
	ELSE
	  GetSymbol;
          Assert((symbol=ident) AND (lexAtt.hashIx = calleeCutPars),
			bad + "Expected 'calleeCutPars'"); 
	  retCutBkt := idBkt;
	END;
      END;
      GetSymbol;
      Assert(symbol = semi,bad + "expected ';'");
      GetSymbol;
    END ParseCommand;

    VAR  dblwrd : RECORD CASE : BOOLEAN OF
		      | TRUE  : flt   : REAL;
		      | FALSE : lo,hi : Card32;
		  END; END;
  BEGIN
    OpenConfigFile;

    bitsInWord    := 32;		(* 64-bit mods jl - June 94 *)
    bytesInWord   := 4;			(* default is 32-bit word   *)
    intMax        := 07FFFFFFFH;
    cardMax       := 0FFFFFFFFH;
    adrSize       := 4;
    displayElSize := 0;

    maxFA := 9;
    maxPA := 9;
    minPA := 9;
    expandTests  := FALSE;		(* default is no expand *)
    refRecords   := FALSE;		(* default is by value  *)
    extRecRetPtr := FALSE;
    extArrRetPtr := FALSE;
    sunStructs   := FALSE;
    gdbSupport   := FALSE;
    gdbXCOFF     := FALSE;
    exceptOK     := FALSE;
    EnterString("stackMarkSize",stackMarkSizeHb);
    EnterString("displayElSize",displayElSizeHb);
    EnterString("jumpTabElSize",jumpTabElSizeHb);
    EnterString("maxFieldAlign",maxFieldAlignHb);
    EnterString("minParamAlign",minParamAlignHb);
    EnterString("maxParamAlign",maxParamAlignHb);
    EnterString("fixedParams",fixParamHb);
    EnterString("stackParams",stkParamHb);
    EnterString("INTERFACE",interfaceHb);
    EnterString("stackInverted",stackInvertedHb);
    EnterString("stackUpright",stackUprightHb);
    EnterString("bigEndian",bigEndianHb);
    EnterString("littleEndian",littleEndianHb);
    EnterString("inlineTests",inlineTestsHb);
    EnterString("refRecords",refRecordsHb);
    EnterString("externRecRetPtr",externRecRetPtrHb);
    EnterString("externArrRetPtr",externArrRetPtrHb);
    EnterString("sunValueStructs",sunValueStructsHb);
    EnterString("calleeCutPars",calleeCutPars);
    EnterString("wordSize64",wordSize64);
    EnterString("gdbStabs",gdbFlag);
    EnterString("gdbStabX",gdbXFlag);
    EnterString("exceptOK",exceptFlag);
    InitScanner;
    WHILE symbol <> eofSy DO
      IF symbol = ident THEN ParseCommand;
      ELSE WHILE (symbol <> ident) AND 
		 (symbol <> eofSy) DO GetSymbol END;
      END;
    END;
    Assert(maxFA <=  8,bad + "maxFieldAlign not set <= 8");
    Assert(minPA <=  8,bad + "minParamAlign not set <= 8");
    Assert(parModeSet, bad + "param mode not set");
    IF maxPA = 9 THEN maxPA := maxFA END;
    FOR index := 1 TO 8 DO
      IF index < maxFA THEN alignMap[index] := CHR(index - 1);
      ELSE alignMap[index] := CHR(maxFA - 1);
      END;
      IF    index < minPA THEN paramMap[CHR(index - 1)] := CHR(minPA - 1);
      ELSIF index < maxPA THEN paramMap[CHR(index - 1)] := CHR(index - 1);
      ELSE                     paramMap[CHR(index - 1)] := CHR(maxPA - 1);
      END;
    END;
    IF stackInverted THEN
      oP1 := 0;
      oP2 := bytesInWord;
      oP3 := 2 * bytesInWord;
      oP4 := 3 * bytesInWord;
      oP5 := 4 * bytesInWord;
      destOffset := stackMarkSize;
    ELSE
      oP1 := -1 * INT(bytesInWord);
      oP2 := -2 * INT(bytesInWord);
      oP3 := -3 * INT(bytesInWord);
      oP4 := -4 * INT(bytesInWord);
      oP5 := -5 * INT(bytesInWord);
      destOffset := -INT(stackMarkSize);
    END;
    wordSize := bytesInWord;
    IF displayElSize = 0 THEN displayElSize := adrSize END;

    IF bigEndian THEN			(* jl Oct 95 *)
      dblwrd.lo := 07FF00000H;
      dblwrd.hi := 0;
    ELSE
      dblwrd.lo := 0;
      dblwrd.hi := 07FF00000H;
    END;
    INFINITY := dblwrd.flt;

  END InitMachineVariables;

  PROCEDURE InitForCLR;
    VAR index : CARDINAL;
  BEGIN
    Assert(stackInverted);
    crossEndian := bigEndian;
    bitsInWord    := 32;
    bytesInWord   := 4;
    intMax        := 07FFFFFFFH;
    cardMax       := 0FFFFFFFFH;
    adrSize       := 4;
    FOR index := 1 TO 8 DO
      IF index < 4 THEN alignMap[index] := CHR(index - 1);
      ELSE alignMap[index] := CHR(3);
      END;
      paramMap[CHR(index - 1)] := CHR(3);
    END;
    expandTests  := FALSE;		(* default is no expand *)
    refRecords   := FALSE;		(* default is by value  *)
    extRecRetPtr := FALSE;
    extArrRetPtr := FALSE;
    sunStructs   := FALSE;
  END InitForCLR;

  VAR card : CARDINAL;
      cPtr : POINTER TO CHAR;

BEGIN
  optDensity :=  5;		(* density of case tables >=  5/16 *)
  defDensity := 10;		(* density of case tables >= 10/16 *)
  parModeSet := FALSE;
 (* find out the endian-ness *)
  card := ORD("?");
  cPtr := SYSTEM.ADR(card);
  bigEndian := NOT (cPtr^ = "?");
END M2MachineConstants.
