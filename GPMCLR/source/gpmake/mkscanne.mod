(*
 * =========== macro processed output from MPP  ==========
 *
 * input file  : mkscanne.mpp
 * time stamp  : 1997:01:22::10:46:50
 *
 * output file : mkscanne.mod
 * created at  : 2004:01:12::14:21:43
 *
 * options ... :  /Ddotnet86
 *
 * =======================================================
 *)

(* -- RCS header --
	$Log:	mkscanne.mpp,v $
Revision 1.2  93/11/03  09:01:19  mboss
Added DEC Alpha changes.

Revision 1.1  93/03/25  14:31:59  mboss
Initial revision

*)
(* 
 *  extracted with 
 * 	    "opsys" == "windows"
 * 	   "endian" == "little"
 *	"processor" == "iap386"
 *)

    (**********************************************************)
    (* THIS PC-VERSION USES LITTLE-ENDIAN PACKING FOR FIXNUMS *)
    (**********************************************************)

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
(*                                                              *)
(*               CUT DOWN VERSION FOR PC GPMAKE                 *)
(*                     dwc September 1991                       *)
(*								*)
(*			: 22-Apr-92 kjg handle comment to eof	*)
(*                      : 28-Oct-93 pms "4" to bytesInWord      *)
(*								*)
(****************************************************************)

IMPLEMENTATION MODULE MkScanner;


FROM Storage IMPORT ALLOCATE;
FROM ProgArgs IMPORT Assert;

FROM MkAlphabets IMPORT TermSymbols, Spellix, Flags, FlagSet,
			ModStateFlags, ModStateSet, SymbolSet,
                        errors, HashBucketType, LexAttType, ConBlock;

FROM MkNameHandler IMPORT MarkInterimSpellix, InterimSpellix,
                          LookupAndEnter, CopyChar, CopyAndHash,
                          MarkEnd, Commit;
FROM MkInOut IMPORT ReadCh, MarkPosAndReadCh, ReadSb, ReadMb;
FROM Ascii IMPORT nul, lf;

  CONST eol     = lf; (* this is the UNIX convention !!! *)
        bytesInWord = 4;
	bytesInReal = 8;

  TYPE  CharSet = SET OF CHAR;

  VAR	ch	: CHAR;		(* = current character	*)
	sb	: CHAR; 	(* = symbol file byte   *)
	mb      : CHAR;         (* = make file byte     *)

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
 *  VAR	symbol : TermSymbols;     (* symbol from input file *)
 *	(* this is a READ ONLY variable, should
 *	   really be a function application *)
 *
 *	symSmbl : TermSymbols;    (* symbol from symbol file *)
 *	(* this is a READ ONLY variable, should
 *	   really be a function application *)
 *
 *      makSmbl : TermSymbols;    (* symbol from make file *)
 *	(* this is a READ ONLY variable, should
 *	   really be a function application *)
 *
 *  VAR	lexAtt : LexAttType;
 *	(* this is a READ ONLY variable, should
 *	   really be a function application *)
 *)

  (* --------------------------------------------- *)
	MODULE CommentsAndPragmas;

	IMPORT ch, ReadCh, symbol, TermSymbols, nul;

        EXPORT ProcessComment;

	PROCEDURE ProcessComment;
	  VAR	nestLevel : CARDINAL;
	 BEGIN (* assert: (old = '(') AND (ch = '*') *)
	  ReadCh(ch); (* get past '*' *)
	  nestLevel := 1;
	  WHILE nestLevel > 0 DO
	    IF ch = nul THEN symbol := errSy; RETURN;
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

	END CommentsAndPragmas;
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
(*
  INC(errFree);
  *)
  REPEAT 
    (* first, protect the ReadCh *)
    IF ch = nul THEN 
      Assert(symbol <> eofSy,"Attempt to read past <EOF>");
      symbol := eofSy; 
      RETURN;
    END; 
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
    | '^' : symbol := upArrow;
    | ':' : IF ch = '=' THEN symbol := assignSy; ReadCh(ch);
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
    | '(' : IF ch = '*' THEN ProcessComment;
	    ELSE symbol := lPar;
	    END;
    | 'a'..'z', 'A'..'Z' , '_' :
	    IF old = '_' THEN 
	      flag := TRUE;
	    ELSE flag := FALSE;
	    END;
	    MarkInterimSpellix;
	    CopyAndHash(old);
	    WHILE ch IN CharSet{'A'..'Z','a'..'z','0'..'9','_'} DO
	      IF ch = '_' THEN
		flag := TRUE;
	      ELSE flag := FALSE;
	      END;
	      CopyAndHash(ch); ReadCh(ch);
	    END; (* while *)
	    MarkEnd();
	    LookupAndEnter(symbol,lexAtt.hashIx);
    | '"', "'" : 
	    MarkInterimSpellix;
	    lexAtt.stringIx := InterimSpellix(); ch1 := ch;
	    WHILE (ch <> old) AND (ch <> eol) DO
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
	    (*
	    IF ch = eol THEN symbol := errSy; END;
	    *)
	    ReadCh(ch); 		    (* dump terminating character *)
    | 1C ..' ' : (* ignore control characters *)
    | '0'..'9' : (*symbol := errSy; *)
    ELSE (*Error(2);*) 				 (* illegal character *)
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
  VAR	dummy : TermSymbols;
	count : CARDINAL;
	cPtr  : ConBlock;
BEGIN
  symSmbl := VAL(TermSymbols,ORD(sb));
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
    | keySy, fixNum    : (* 4 bytes at present (M23 uses 6!) *)
        (* 
         *  little-endian
         *)
      		  FOR count := 0 TO bytesInWord - 1 DO
		    bytes[count] := sb; ReadSb(sb);
                  END;
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
                  strHigh := InterimSpellix() - lexAtt.stringIx;
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
    | heapConst : ReadSb(sb);
        (* 
         *  little-endian
         *)
      		  FOR count := 0 TO bytesInWord - 1 DO
		    bytes[count] := sb; ReadSb(sb);
                  END;
(* this close WAS after adrsValue := cPtr; !! *)
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

PROCEDURE GetMakSmbl;
(* precondition  : there is an attached make file which
	   has been initialized by InitMakScan;
   postcondition : the variable makSmbl holds the next symbol.
	   The attribute variable lexAtt holds any value. If the symbol
	   is an identifier, then .hashIx holds the current table index
	   for the id. If the symbol is a numeric literal, then
	   .fixValue contains the value. *)
  CONST mark  = 0C; (* record separator *)
  VAR	dummy : TermSymbols;
	count : CARDINAL;
BEGIN
  makSmbl := VAL(TermSymbols,ORD(mb));
  IF makSmbl = eofSy THEN RETURN END;
  ReadMb(mb);
  WITH lexAtt DO	(* read extra bytes *)
    CASE makSmbl OF
    | beginSy, definitionSy, moduleSy : (* ReadMb(mb); *)
    | ident     : MarkInterimSpellix;
                  WHILE mb <> mark DO
                    CopyAndHash(mb);
                    ReadMb(mb);
                  END;
                  MarkEnd();
                  ReadMb(mb); (* read past mark *)
                  LookupAndEnter(dummy,hashIx);
    | exceptSy : (* ignore following "bytesInWord" bytes - was 4 *)
                  FOR count := 1 TO bytesInWord DO
		      ReadMb(mb);
                  END;
    | fixNum    :
        (* 
         *  little-endian
         *)
      		  FOR count := 0 TO bytesInWord - 1 DO
		    bytes[count] := mb; 
		    ReadMb(mb);
                  END;
    ELSE (* Assert(FALSE);  *)
    END; (* case *)
  END; (* with *)
END GetMakSmbl;

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
(*
PROCEDURE RelaxLexicalRules;
BEGIN
  relax := TRUE;
END RelaxLexicalRules;
*)
PROCEDURE InitSymScan;
(* precondition  : there is an attached symbol file stream;
   postcondition : the sym-file stream is initialized, and
                   the first sySmbl is already fetched.    *)
BEGIN
  ReadSb(sb);                                  (* read first byte *)
  GetSymSmbl;                           (* establish precondition *)
END InitSymScan;

PROCEDURE InitMakScan;
(* precondition  : there is an attached make file stream;
   postcondition : the makefile stream is initialized, and the
		   first makSym is already fetched.    *)
BEGIN
  ReadMb(mb);
  GetMakSmbl;
END InitMakScan;


END MkScanner.
