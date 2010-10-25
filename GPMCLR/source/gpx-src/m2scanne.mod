(****************************************************************)
(*                                                              *)
(*             Modula-2 Compiler Source Module                  *)
(*                                                              *)
(*                Lexical Scanner for Compiler                  *)
(*        Nested modules contain string and hash tables.        *)
(*                                                              *)
(*           (c) copyright 1987 SoftWare Automata.              *)
(*                                                              *)
(*      original module : kjg july 1987                         *)
(*      modifications   : bigSetCon lex conventions; 20-Nov-87  *)
(*                        06-Mar-88 correcting real format      *)
(*			: 24-Mar-88 adding charLit to           *)
(*                        GetSymSmbl                            *)
(*			: 17-Feb-89 removing $L pragma          *)
(*                        and fixing ParseReal fraction part    *)
(*			: 08-Aug-89 new underscore conventions  *)
(*			: 28-Aug-89 split error 4 to 4 & 7      *)
(*			:  6-Oct-89 constant HUGE and new exps  *)
(*			: 30-Nov-89 heap constant scanning	*)
(*			: 12-Jun-90 new handling of charNums    *)
(*			:  6-Jul-90 sync primitives for parser  *)
(*			: 23-Jun-91 dollar signs for Apollo	*)
(*			: 14-May-92 RelaxLimit call		*)
(*								*)
(*   =============== merged mips and i386 source ============	*)
(*			   kjg 22 Mar 93			*)
(*                                                              *)
(****************************************************************
$Log: m2scanne.mod,v $
Revision 1.7  1997/01/16 05:00:20  gough
        delete reference to RelaxLimit.
        New procedures PshSymScanState, PopSymScanState.

Revision 1.6  1996/08/26 07:25:01  lederman
using RealStr.StrToReal now instead

Revision 1.5  1996/08/22 09:58:14  lederman
replace ParseReal & ParseExp with RealStr.Take()

Revision 1.4  1995/10/18 00:42:38  lederman
give warning 511 (instead of error 6) for floating-point overflow
also creation of INFINITY (was HUGE) moved to M2MachineConstants

Revision 1.3  1994/08/02 03:55:18  lederman
added extra glyph recognition from via-C version

# Revision 1.2  1994/07/01  05:31:26  lederman
# calc HUGE endian dependant;  read numbers from sym file in 'host' size
# -- --- this is probably wrong ---
#
# Revision 1.1  1994/04/07  05:17:51  lederman
# Initial revision
#
*****************************************************************
Revision 1.4  94/03/23  14:48:25  gough
check on overflow for number scanning in this module
*****************************************************************)

IMPLEMENTATION MODULE M2Scanner;

FROM Storage  IMPORT ALLOCATE;
FROM Ascii    IMPORT nul, lf;
FROM RealStr  IMPORT StrToReal, ConvResults;

FROM M2Alphabets IMPORT TerminalSymbols, Spellix, Flags, FlagSet,
                        HashBucketType, LexAttType, ConBlock;

FROM M2NameHandler IMPORT MarkInterimSpellix, InterimSpellix,
                          LookupAndEnter, CopyChar, CopyAndHash,
                          MarkEnd, Commit;

FROM M2MachineConstants IMPORT bytesInWord, bytesInReal, INFINITY;
FROM M2InOut IMPORT Error, ReadCh, MarkPosAndReadCh, ReadSb;

  CONST eol     = lf; (* this is the UNIX convention !!! *)

  TYPE  CharSet = SET OF CHAR;

  VAR	ch	: CHAR;		(* = current character	*)
	sb	: CHAR; 	(* = symbol file byte   *)

	(* Modula requires two characters of lookahead  *)
	(* to resolve 25.. from 25.6, and so on... So	*)
				(* if oops is true then *)
	oops	: BOOLEAN;	(* the number scanner	*)
				(* had to put back a	*)
	(* fullstop. Nasty, but this is better than a	*)
	(* Boolean test on every call of ReadChar!	*)

        relax   : BOOLEAN;

  VAR   errFree : INTEGER; (* number of error free tokens parsed *)
  CONST syncCount = 2;

(*
 *  VAR	symbol : TerminalSymbols;     (* symbol from input file *)
 *	(* this is a READ ONLY variable, should
 *	   really be a function application *)
 *
 *	symSmbl : TerminalSymbols;    (* symbol from symbol file *)
 *	(* this is a READ ONLY variable, should
 *	   really be a function application *)
 *
 *  VAR	lexAtt : LexAttType;
 *	(* this is a READ ONLY variable, should
 *	   really be a function application *)
 *)

  (* --------------------------------------------- *)
  (* ----- parser synchronization procedures ----- *)

        PROCEDURE IsSynchronized() : BOOLEAN;
        BEGIN
	  RETURN errFree > 0;
	END IsSynchronized;

	PROCEDURE StartSyncCount();
        BEGIN
	  errFree := - syncCount;
        END StartSyncCount;

  (* --------------------------------------------- *)

	PROCEDURE GetContextMark();
	  VAR sDummy : TerminalSymbols;
	BEGIN (* assert: ch = "!" *)
	  ReadCh(ch);
	  MarkInterimSpellix;
	  WHILE ch IN CharSet{"A".."Z","_"} DO
	    CopyAndHash(ch); ReadCh(ch);
	  END;
	  MarkEnd();
	  LookupAndEnter(sDummy,lexAtt.hashIx);
	END GetContextMark;
	(* "SYSTEM", "LIBRARY", "FOREIGN" etc. *)

	(************************************************)

	MODULE CommentsAndPragmas;

	IMPORT ch, ReadCh, symbol, TerminalSymbols, lexAtt,
	       GetContextMark, LexAttType, Flags, FlagSet, Error, nul;

        EXPORT ProcessComment, CurrentFlags, SetFlagOn,
               InitializeOptions;

	CONST	defaultFlags = FlagSet {
			indexTests,rangeTests,ovfloTests,stackTests};

	CONST	depth = 7; (* maximum stack depth is as given	*)
			   (* further pushes lose bottom elem's *)

	VAR	flags : FlagSet;
		stack : ARRAY [indexTests .. compact] OF
			  RECORD
			    el : ARRAY[0..depth] OF BOOLEAN;
			    sp : CARDINAL;
			  END;

	PROCEDURE CurrentFlags() : FlagSet;
	BEGIN
	  RETURN flags;
	END CurrentFlags;

	PROCEDURE SetFlagOn(flg : Flags);
	BEGIN
	  INCL(flags,flg);
	END SetFlagOn;

	PROCEDURE InitializeOptions(init : FlagSet);
	BEGIN (* allows initialization from command line *)
	  flags := init;
	END InitializeOptions;

	PROCEDURE Push(f : Flags);
	  VAR i : CARDINAL;
	BEGIN
	  WITH stack[f] DO
	    IF sp <= depth THEN el[sp] := (f IN flags); INC(sp);
	    ELSE (* sp = depth + 1 *)
	      FOR i := 1 TO depth DO el[i-1] := el[i] END;
	      el[depth] := (f IN flags);
	    END;
	  END
	END Push;

	PROCEDURE Pop(f : Flags) : BOOLEAN;
	BEGIN
	  WITH stack[f] DO
	    IF sp > 0 THEN DEC(sp) ELSE Error(504) END;
	    RETURN el[sp];
	  END
	END Pop;

	PROCEDURE ProcessComment;
	  VAR	nestLevel : CARDINAL; flg : Flags;
	 BEGIN (* assert: (old = '(') AND (ch = '*') *)
	  ReadCh(ch); (* get past '*' *)
	  nestLevel := 1;
	  (* check for pragmas *)
	  LOOP
	    WHILE ch <= ' ' DO ReadCh(ch) END;
	    IF ch <> '$' THEN EXIT END;
	    ReadCh(ch);
	    CASE ch OF
	      'S' : flg := stackTests;
	    | 'R' : flg := rangeTests;
	    | 'F' : flg := fastCode;
	    | 'C' : flg := compact;
	    | 'I' : flg := indexTests;
	    | 'T' : flg := ovfloTests;
	    ELSE Error(503); EXIT; (* invalid pragma selector *)
	    END;
	    ReadCh(ch);
	    IF ch = '=' THEN
	      IF Pop(flg) THEN INCL(flags,flg)
	      		  ELSE EXCL(flags,flg)
	      END;
	    ELSIF ch = '+' THEN Push(flg); INCL(flags,flg);
	    ELSIF ch = '-' THEN Push(flg); EXCL(flags,flg);
	    ELSE Error(505); (* invalid pragma operator *)
	    END;
	    WHILE ch <= ' ' DO ReadCh(ch) END;
	    IF ch = ',' THEN ReadCh(ch) END;
	  END; (* pragma loop *)
	  IF ch = "!" THEN GetContextMark END;
	  WHILE nestLevel > 0 DO
	    IF ch = nul THEN Error(3); RETURN;
	    ELSIF ch = '*' THEN
	      ReadCh(ch);
	      IF ch = ')' THEN
		DEC(nestLevel); ReadCh(ch);
		(* else nothing *)
	      END;
	    ELSIF ch = '(' THEN
	      ReadCh(ch);
	      IF ch = '*' THEN
		INC(nestLevel); ReadCh(ch);
		(* else nothing *)
	      END;
	    ELSE ReadCh(ch);
	    END;
	  END; (* while *)
	  (* assert: (nestLevel = 0) & ch past last ')' *)
	END ProcessComment;

	  VAR ix : Flags;

	BEGIN
	  FOR ix := indexTests TO compact DO
	    stack[ix].sp := 0;
	  END;
	  flags := defaultFlags;
	END CommentsAndPragmas;

	(************************************************)

MODULE Numbers;

	IMPORT ch, ReadCh, symbol, TerminalSymbols, lexAtt, nul, INFINITY,
	       CharSet, oops, LexAttType, Error, StrToReal, ConvResults;

	EXPORT ScanNumber;
	  

	  CONST	max2 = 399; (* max length of numeric literals *)
		max1 = max2 - 2;

		decDigit = CharSet{'0' .. '9'};


	  VAR	buf : ARRAY [0..max2] OF CHAR;
		ix  : [0..max2];


	PROCEDURE ParseOct;
	  (* assert: buf[ix - 1] contains a B or a C
		     buf[0] is a DECIMAL digit 		*)
	  VAR	value, old, i, dig : CARDINAL;
	BEGIN
	  i := 0; value := 0; (* must test buf[0] also	*)
  (*$T-*) dig := ORD(buf[0]) - ORD('0');
	  (* ALL invalid chars give dig > 7 *)
	  WHILE dig < 8 DO
	    old   := value;
	    value := value * 8 + dig;
	    INC(i);
	    dig := ORD(buf[i]) - ORD('0');
	    IF (old > MAX(CARDINAL) DIV 8) OR (value < old) THEN
	      Error(7);
	    END;
  (*$T=*) END;
	  IF i <> ix - 1 THEN Error(5); value := 0; END;
	  IF symbol = charNum THEN
	    IF value > 377B THEN Error(8) END; (* too big *)
	    (* anyway, just in case the machine sign-propagates *)
	    lexAtt.charValue := CHR(value MOD 400B);
	    (*
	     *  the next two lines are added to allow
	     *  charNums to be treated as S1s in certain
	     *  contexts. This is needed to allow the
	     *  string concatenation extension.
	     *
	     *  The actual string is not placed in the
	     *  string table, with the distinguished 
	     *  value stringIx = 0 denoting this.
	     *  The actual string is constructed by 
	     *  M2ObjectCode during literal dumping.
	     *)
	    lexAtt.stringIx  := 0;	(* 12-Jun-90 *)
	    lexAtt.strHigh   := 1;	(* 12-Jun-90 *)
	  ELSE (* symbol = fixNum *)
	    lexAtt.fixValue := value;
	  END;
	END ParseOct;

	PROCEDURE ParseDec;
	  (* assert: buf[ix] contains a nul;
		     buf[0] is a DECIMAL digit 		*)
	  VAR	value, old, i, dig : CARDINAL;
	BEGIN
	  value := ORD(buf[0]) - ORD('0'); i := 1;
  (*$T-*) dig := ORD(buf[1]) - ORD('0');
	  (* ALL invalid chars give dig > 9 *)
	  WHILE dig < 10 DO
	    old := value;
	    value := value * 10 + dig;
	    INC(i);
	    dig := ORD(buf[i]) - ORD('0');
	    IF (old > MAX(CARDINAL) DIV 10) OR (value < old) THEN
	      Error(7);
	    END;
  (*$T=*) END;
	  IF i <> ix THEN Error(5); value := 0; END;
	  lexAtt.fixValue := value;
	END ParseDec;

	PROCEDURE ParseHex;
	  (* assert: buf[ix-1] contains H, buf[0] is decimal *)
	  VAR value : CARDINAL; old, i, digit : CARDINAL;

	  (*$S-*)
	  PROCEDURE DigValue(c : CHAR) : CARDINAL;
	  BEGIN (* << ASCII specific >> *)
	    IF c >= 'A' THEN RETURN ORD(c) - ORD('A') + 10;
	    (* chars > 'F' return > 15 => illegal *)
	    ELSIF c <= '9' THEN (* c < '0' retns >> 15 *)
            (*$T-*) RETURN ORD(c) - ORD('0'); (*$T=*)
	    ELSE RETURN 16 (* anything > 15 gets caught *)
	    END;
	  END DigValue;
	  (*$S=*)

	BEGIN
	  value := (DigValue(buf[0]));
	  digit := DigValue(buf[1]); i := 1;
  (*$T-*) WHILE digit < 16 DO
	    old := value;
	    value := value * 16 + digit;
	    INC(i); digit := DigValue(buf[i]);
	    IF (old > MAX(CARDINAL) DIV 16) OR (value < old) THEN
	      Error(7);
	    END;
  (*$T=*) END;
	  IF i <> ix - 1 THEN Error(5); value := 0; END;
	  lexAtt.fixValue := value;
	END ParseHex;


	PROCEDURE ScanNumber(old : CHAR);
	(* old is first character of number,
	   guaranteed to be a decimal digit. *)
	  VAR format : ConvResults;
	BEGIN
	  buf[0] := old; ix := 1;
	  WHILE ch IN decDigit + CharSet{'A'..'F','H'} DO
	    buf[ix] := ch; ReadCh(ch);
	    IF ix < max1 THEN INC(ix) END; (* room for '.' *)
	  END;
	  IF ix = max1 THEN Error(7) END;
	  (* assert: max2 > ix >= 1 *)
	  (* and now ... CASE buf[ix - 1] OF *)
	  CASE buf[ix - 1] OF
	    '0'..'9' : (* some kind of decimal number *)
		  IF ch <> '.' THEN (* decimal fixNum *)
		    symbol := fixNum;
		    buf[ix] := nul;
		    ParseDec;
		  ELSE (* ch = '.' worry about "oops" *)
		    ReadCh(ch);
		    IF ch = '.' THEN
		      oops := TRUE;
		      symbol := fixNum;
		      buf[ix] := nul;
		      ParseDec;
		    ELSE (* floatNum *)
		      symbol := floatNum;
		      buf[ix] := '.'; INC(ix);
		      WHILE ch IN decDigit DO
			buf[ix] := ch;
			IF ix < max2 THEN INC(ix) END;
			ReadCh(ch);
		      END;
		      IF ch = 'E' THEN (* exponent scan *)
			buf[ix] := ch;
			IF ix < max2 THEN INC(ix) END;
			ReadCh(ch);
			IF (ch = '+') OR (ch = '-') THEN
			  buf[ix] := ch;
			  IF ix < max2 THEN INC(ix) END;
			  ReadCh(ch);
			END;
			IF ch IN decDigit THEN
			  WHILE ch IN decDigit DO
			    buf[ix] := ch;
			    IF ix < max2 THEN INC(ix) END;
			    ReadCh(ch);
			  END;
			ELSE Error(4);
			END;
		      END; (* exponent scan *)
		      IF ix = max2 THEN Error(7) END;
		      buf[ix] := nul;
		      StrToReal(buf,lexAtt.floatValue,format);
		      IF format <> strAllRight THEN
			IF format = strOutOfRange THEN
			  IF lexAtt.floatValue < 0.0 THEN
			    lexAtt.floatValue := -INFINITY;
			  ELSE
			    lexAtt.floatValue := +INFINITY;
			  END;
			  Error(511);
			ELSE Error(4); (* "cannot happen" *)
			END;
		      END;
		    END; (* floatNum *)
		  END; (* '0' .. '9' *)
	  | 'B' : symbol := fixNum;  ParseOct;
	  | 'C' : symbol := charNum; ParseOct;
	  | 'H' : symbol := fixNum;  ParseHex;
	  ELSE Error(5);
	  END; (* case *)
	END ScanNumber;
END Numbers;

	(************************************************)

PROCEDURE GetSymbol;
(* precondition  : there is an attached input stream which
		   has been initialized by InitScanner;
   postcondition : the variable symbol holds the next symbol.
		   The attribute variable lexAtt holds any value.
		   If the symbol is an identifier, then .hashIx
		   holds the current hash table index for the id.
		   If the symbol is a numeric literal, then
		   .fixValue, .charValue or .floatValue contains
		   the value. If the symbol is a string, then
		   .stringIx has the stringtable index.		*)

  VAR	old, ch1 : CHAR;	(* = previous character *)
	high : CARDINAL;	(* almost  HIGH(string) *)
        flag : BOOLEAN;		(* used for underscores *)

BEGIN  (* assert: current ch is past end of last lexeme *)
  INC(errFree);
  REPEAT
    (* first, protect the ReadCh *)
    IF ch = nul THEN symbol := eofSy; RETURN END; 
    symbol := errSy;
    old := ch; MarkPosAndReadCh(ch);
    CASE old OF
      '*' : symbol := star;	
    | '/' : symbol := slash;	
    | '~' : symbol := notSy;	
    | '+' : symbol := plus;	
    | '&' : symbol := andSy;	
    | '-' : symbol := minus;	
    | '=' : symbol := equals;	
    | '#' : symbol := notEq;	
    | '[' : symbol := lBrac;	
    | ']' : symbol := rBrac;	
    | '{' : symbol := lCurly;	
    | '}' : symbol := rCurly;	
    | ')' : symbol := rPar;
    | ',' : symbol := comma;	
    | ';' : symbol := semi;
    | '|' : symbol := bar;
    | '!' : IF ch = ')' THEN
               symbol := rBrac;
               ReadCh(ch);
            ELSE
               symbol := bar;
            END;
    | '^' : symbol := upArrow;
    | '@' : symbol := upArrow;
    | ':' : IF ch = '=' THEN 
               symbol := assignSy; 
               ReadCh(ch);
            ELSIF ch = ')' THEN
               symbol := rCurly;
               ReadCh(ch);
	    ELSE symbol := colon;
	    END;
    | '.' : IF oops THEN oops := FALSE; symbol := dotDot;
	    ELSIF ch = '.' THEN symbol := dotDot; ReadCh(ch);
	    ELSE symbol := dot;
	    END;
    | '>' : IF ch = '=' THEN symbol := grEqual; ReadCh(ch);
	    ELSE symbol := greater;
	    END;
    | '<' : IF ch = '=' THEN symbol := lessEq; ReadCh(ch);
	    ELSIF ch = '>' THEN symbol := notEq; ReadCh(ch);
	    ELSE symbol := less;
	    END;
    | '(' : IF ch = '*' THEN 
               ProcessComment;
            ELSIF ch = '!' THEN
               symbol := lBrac;
               ReadCh(ch);
            ELSIF ch = ':' THEN
               symbol := lCurly;
               ReadCh(ch);
	    ELSE symbol := lPar;
	    END;
    | 'a'..'z', 'A'..'Z' , '_' :
	    IF old = '_' THEN 
	      flag := TRUE;
	      IF NOT relax THEN Error(9) END;
	    ELSE flag := FALSE;
	    END;
	    MarkInterimSpellix;
	    CopyAndHash(old);
	    WHILE ch IN CharSet{'A'..'Z','a'..'z','0'..'9','_'} DO
	      IF ch = '_' THEN
		IF flag AND NOT relax THEN Error(9) END;
		flag := TRUE;
	      ELSE flag := FALSE;
	      END;
	      CopyAndHash(ch); ReadCh(ch);
	    END; (* while *)
	    MarkEnd();
	    IF flag AND NOT relax THEN Error(9) END;
	    LookupAndEnter(symbol,lexAtt.hashIx);
    | '"', "'" : 
	    MarkInterimSpellix;
	    lexAtt.stringIx := InterimSpellix(); ch1 := ch;
	    WHILE (ch <> old) AND (ch <> eol) AND (ch <> nul) DO
	      CopyChar(ch); ReadCh(ch); (* inc's InterimSpellix *)
	    END;
	    MarkEnd;
            (* now get HIGH of string *)
            MarkInterimSpellix; (* again *)
            high := InterimSpellix() - lexAtt.stringIx;
            DEC(high);
            IF high <= 1 THEN
              symbol := charLit; 
	      IF high = 0 THEN lexAtt.charValue := nul;
	      ELSE lexAtt.charValue := ch1;
	      END;
            ELSE symbol := litstring;
            END;
	    lexAtt.strHigh := high;
	    IF ch = eol THEN Error(1) END;  (* unterminated string *)
	    ReadCh(ch); 		    (* dump terminating character *)
    | 1C ..' ' : (* ignore control characters *)
    | '0'..'9' : ScanNumber(old);
    ELSE Error(2); 				 (* illegal character *)
    END; (* case ch of *)
  UNTIL symbol <> errSy;
  (* assert: ch is one past end of lexeme, or at end of file *)
END GetSymbol;

PROCEDURE GetSymSmbl;
(* precondition  : there is an attached symbol file which
	   has been initialized by InitSymScan;
   postcondition : the variable symSmbl holds the next symbol.
	   The attribute variable lexAtt holds any value. If the symbol
	   is an identifier, then .hashIx holds the current table index
	   for the id. If the symbol is a numeric literal, then
	   .fixValue, .charValue or .floatValue contains the value. If
	   the symbol is a string, then .stringIx has the stringtable 
	   index, if the symbol is a big set then .patternIx points
	   to the literal.		*)
  CONST mark  = 0C; (* record separator *)
  VAR	dummy : TerminalSymbols;
	count : CARDINAL;
	scale : CARDINAL;
	cPtr  : ConBlock;
BEGIN
  symSmbl := VAL(TerminalSymbols,ORD(sb));
  IF symSmbl = eofSy THEN RETURN END;
  ReadSb(sb);
  WITH lexAtt DO	(* read extra bytes *)
    CASE symSmbl OF
    | charNum   : charValue := sb;
		  stringIx  := 0;	(* 12-Jun-90 *)
		  strHigh   := 1;	(* 12-Jun-90 *)
		  ReadSb(sb);
    | charLit   : MarkInterimSpellix;
                  stringIx := InterimSpellix();
                  CopyChar(sb); MarkEnd();
                  charValue := sb; ReadSb(sb);
    | keySy, fixNum : (* 4 bytes at present (M23 uses 6!) *)
		  fixValue := ORD(sb); ReadSb(sb); 
		  scale := 1;
		  FOR count := 2 TO bytesInWord DO
		    scale := scale * 100H;
		    INC(fixValue,ORD(sb) * scale); ReadSb(sb); 
		  END;
	(*
         *  endian sensitive
         *
	 *    	  FOR count := 0 TO bytesInWord - 1 DO
	 *	    bytes[count] := sb; ReadSb(sb);
	 *        END;
	 *)
    | floatNum  : FOR count := 0 TO bytesInReal - 1 DO
                    bytes[count] := sb; ReadSb(sb);
                  END;
    | litstring : MarkInterimSpellix;
                  stringIx := InterimSpellix();
                  WHILE sb <> mark DO
                    CopyChar(sb);
                    ReadSb(sb);
                  END;
                  MarkEnd(); ReadSb(sb);
                  (* now get HIGH of string *)
                  MarkInterimSpellix; (* again *)
                  strHigh := InterimSpellix() - stringIx;
                  DEC(strHigh);
    | bigSetCon : MarkInterimSpellix;
                  count := ORD(sb); ReadSb(sb);
                  patternIx := InterimSpellix();
                  WHILE count > 0 DO
                    CopyChar(sb);
                    DEC(count);

                    ReadSb(sb);
                  END; (* commit is necessary *)
                  Commit();
    | heapConst : 
		  ReadSb(sb); (* read past fixnum marker *)
		  fixValue := ORD(sb); ReadSb(sb); 
		  scale := 1;
		  FOR count := 2 TO bytesInWord DO
		    scale := scale * 100H;
		    INC(fixValue,ORD(sb) * scale); ReadSb(sb); 
		  END;
        (* 
         *  endian sensitive
         *
	 *        ReadSb(sb);
      	 *	  FOR count := 0 TO bytesInWord - 1 DO
	 *	    bytes[count] := sb; ReadSb(sb);
         *        END;
	 *)
		  ALLOCATE(cPtr,fixValue);
		  FOR count := 0 TO fixValue - 1 DO
		    cPtr^[count] := sb;
		    ReadSb(sb);
		  END;
		  adrsValue := cPtr;
    | ident     : MarkInterimSpellix;
                  WHILE sb <> mark DO
                    CopyAndHash(sb);
                    ReadSb(sb);
                  END;
                  MarkEnd();
                  ReadSb(sb); (* read past mark *)
                  LookupAndEnter(dummy,hashIx);
    ELSE (* nothing *)
    END; (* case *)
  END (* with *)
END GetSymSmbl;

PROCEDURE InitScanner;
(* precondition  : there is an attached input stream;
   postcondition : the input stream is initialized, and
                   the first symbol is already fetched.        *)
BEGIN
  oops := FALSE; 
  relax := FALSE;
  errFree := 1;
  lexAtt.fixValue := 0;
  ReadCh(ch);
  GetSymbol;
END InitScanner;

PROCEDURE RelaxLexicalRules;
BEGIN
  relax := TRUE;
END RelaxLexicalRules;

(* =============================================================== *)
MODULE SymScanState;
  IMPORT TerminalSymbols, sb, symSmbl, lexAtt, LexAttType, GetSymSmbl, ReadSb;
  EXPORT PopSymScanState, PshSymScanState;

TYPE State =  RECORD
		sb : CHAR;
		sy : TerminalSymbols;
		at : LexAttType;
	      END;

VAR  stateStack : ARRAY [0 .. 63] OF State;
     topOfStack : [0 .. 63];

PROCEDURE PshSymScanState;
(* precondition  : there is an attached symbol file stream;
   postcondition : the sym-file stream is initialized, and
                   the first sySmbl is already fetched.    *)
BEGIN
  stateStack[topOfStack].sb := sb;
  stateStack[topOfStack].sy := symSmbl;
  stateStack[topOfStack].at := lexAtt;
  INC(topOfStack);
  ReadSb(sb);                                  (* read first byte *)
  GetSymSmbl;                           (* establish precondition *)
END PshSymScanState;

PROCEDURE PopSymScanState;
BEGIN
  DEC(topOfStack);
  sb      := stateStack[topOfStack].sb;
  symSmbl := stateStack[topOfStack].sy;
  lexAtt  := stateStack[topOfStack].at;
END PopSymScanState;

BEGIN
  topOfStack := 0;
END SymScanState;
(* =============================================================== *)

(*
PROCEDURE InitSymScan;
(* precondition  : there is an attached symbol file stream;
   postcondition : the sym-file stream is initialized, and
                   the first sySmbl is already fetched.    *)
BEGIN
  ReadSb(sb);                                  (* read first byte *)
  GetSymSmbl;                           (* establish precondition *)
END InitSymScan;
 *)
END M2Scanner.
