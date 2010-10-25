(*
 * =========== macro processed output from MPP  ==========
 *
 * input file  : mpp.mpp
 * time stamp  : 2004:01:12::04:21:11
 *
 * output file : mpp.mod
 * created at  : 2004:01:12::14:21:43
 *
 * options ... :  /Ddotnet86
 *
 * =======================================================
 *)


(* 
 *  extracted with 
 * 	    "opsys" == "windows"
 * 	   "endian" == "little"
 *	"processor" == "iap386"
 *)

(****************************************************************)
(*                                                              *)
(*                Modula-2 Macro Pre-processor			*)
(*                                                              *)
(*                        MAIN MODULE                           *)
(*                                                              *)
(*     (c) copyright 1990 Faculty of Information Technology     *)
(*                                                              *)
(*      original module : kjg December 1990                     *)
(*      modifications   : kjg 6-Jan-90 include files from path  *)
(*			: kjg 5-Mar-90 announce multiple fnames *)
(*			: jrh 15-Sep-92 pc version: ignore cr,^Z*)
(*			: kjg 28-Sep-92 fix "" in GetSymbol     *)
(*                      : pms 12-Nov-93 fixed endless loop if   *)
(*                                      unclosed comment        *)
(*                                                              *)
(****************************************************************)
(*  NOTE: kjg January 2004                                      *)
(*  The CLR version of this application is significantly more   *)
(*  complex than the UNIX versions, since this application must *)
(*  expand command line arguments that contain wildcards.       *)
(****************************************************************)


MODULE MPP; (* Modula 2 macro preprocessor for gpm *)

  IMPORT TextInOut, StdError, Ascii, Storage, 
        InOut, UxFiles, SysClock, AsciiTime, PathLookup, Wildcards, SYSTEM;

  FROM CardSequences IMPORT
	InitSequence, InitCursor, LinkRight, GetNext, 
	Ended, IsEmpty, ElemPtr, Sequence;

  FROM CharInfo IMPORT 
	IsLetter;

  FROM UxFiles IMPORT 
	ModifyTime, OpenMode, ReadByte, WriteByte, EndFile;

  FROM ProgArgs IMPORT 
	ArgNumber, GetArg, EnvironString;

  (* --------------------------------------------------- *)

  TYPE SymbolType = (eof, eol, ifs, define, undef, ifdef,
			ifndef, else, endif, ident,
			include, message,
			other, error, 
			equ, neq, bad);
       SymbolSet  = SET OF SymbolType;

  VAR   symbol : SymbolType;
  VAR   errors : BOOLEAN;
	debug  : BOOLEAN;
	announce  : BOOLEAN;		(* if multiple files,  *)
					(* ==> print file name *)

  CONST emptySpx  = 0;
        tabMax    = 40 * 1024 - 1;
        EOF       = CHR(255);
  TYPE  Spellix   = [0 .. tabMax];


  PROCEDURE Table(spx : Spellix) : CHAR; FORWARD;
  PROCEDURE SymExtract(spx : Spellix;
		   VAR str : ARRAY OF CHAR); FORWARD;

  (* ========================================== *)
  MODULE InputOutput;

    IMPORT ReadByte, WriteByte, EndFile, OpenMode, Ascii,
	errors, TextInOut, StdError, Table, SymExtract,
	PathLookup, EnvironString, debug, EOF,
	symbol, emptySpx, SymbolType, Spellix, UxFiles;

    EXPORT Read, WriteRead, Write,
	FatalError, 
	SaveAndOpen, CloseAndRestore,
	input, output, name, MessageSpx,
	InitializeInputStack, ch,
	SpxError, SpxWarning, Message, WriteFilePos;

    (* ====================================== *)
    VAR input  : UxFiles.File;
	output : UxFiles.File;
        name   : Spellix;	(* name of current file  *)
	line   : CARDINAL;
	ch     : CHAR;		(* global state variable *)

    TYPE InStream = RECORD
		      fil : UxFiles.File;
		      chr : CHAR;
		      sym : SymbolType;
		      lin : CARDINAL;
		      nam : Spellix;
		    END;

    VAR stack  : ARRAY [0 .. 15] OF InStream;
	oldFil : [0 .. 15];

    VAR m2symPath,		(* the path $M2SYM   *)
	absName  : 		(* the abs file path *)
		ARRAY [0 .. 1023] OF CHAR;

    PROCEDURE InitializeInputStack();
    BEGIN
      oldFil := 0;
      input  := NIL;
      ch     := Ascii.lf;
      symbol := eof;
      name   := emptySpx;
    END InitializeInputStack;

    PROCEDURE SaveAndOpen(spx : Spellix;
			  pth : BOOLEAN;
		      VAR ok  : BOOLEAN);
      VAR temp : UxFiles.File;
	  str  : ARRAY [0 .. 1023] OF CHAR;
    BEGIN
      SymExtract(spx,str);
      PathLookup.FindAndOpen(".",str,absName,temp);
      IF (temp = NIL) AND pth THEN
	PathLookup.FindAndOpen(m2symPath,str,absName,temp);
      END;
      ok := temp <> NIL;
      IF ok THEN
	IF debug THEN
	  IF pth THEN		(* opening include file  *)
	    WriteFilePos();
	    StdError.WriteString(' including file "');
	  ELSE			(* opening the base file *)
	    StdError.WriteString('mpp: Opening base file "');
	  END;
	  StdError.WriteString(absName);
	  StdError.Write('"');
	  StdError.WriteLn;
	END;
        stack[oldFil].fil := input;
        stack[oldFil].chr := ch;
        stack[oldFil].sym := symbol;
        stack[oldFil].lin := line;
	stack[oldFil].nam := name;
        INC(oldFil);
        input := temp;
	name  := spx;
	line  := 1;
      END;
    END SaveAndOpen;

    PROCEDURE CloseAndRestore;
      VAR ok : BOOLEAN;
    BEGIN
      IF oldFil = 1 THEN 
	IF ch = EOF THEN FatalError("unexpected end of file");
	ELSE ch := "";
        END;
      ELSE 
        UxFiles.Close(input,ok);
	DEC(oldFil);
	input  := stack[oldFil].fil;
	ch     := stack[oldFil].chr;
        name   := stack[oldFil].nam;
        line   := stack[oldFil].lin;
	symbol := stack[oldFil].sym;
      END;
    END CloseAndRestore;

    PROCEDURE MessageSpx(spx : Spellix);
      VAR tCh : CHAR;
    BEGIN
        tCh := Table(spx);
        WHILE tCh <> "" DO
  	  StdError.Write(tCh); INC(spx);
	  tCh := Table(spx);
        END;
    END MessageSpx;

    PROCEDURE WriteFilePos();
    BEGIN
      StdError.Write('"');
      MessageSpx(name);
      StdError.WriteString('":line ');
      (*
       *  a tricky correction ...
       *  the line count may have just been changed
       *)
      StdError.WriteCard(line,0);
      StdError.Write(' ');
    END WriteFilePos;

    PROCEDURE FatalError(str : ARRAY OF CHAR);
    BEGIN
      StdError.WriteString("mpp: fatal error: ");
      StdError.WriteString(str); 
      WriteFilePos();
      StdError.WriteLn;
      HALT;
    END FatalError;
  
    PROCEDURE SpxWarning(spx : Spellix;
			 str : ARRAY OF CHAR);
    BEGIN
      StdError.WriteString("mpp: warning: ");
      StdError.WriteString(str);
      IF spx <> 0 THEN
	StdError.WriteString(' <');
	MessageSpx(spx);
	StdError.WriteString('> ');
      ELSE StdError.Write(" ");
      END;
      WriteFilePos();
      StdError.WriteLn;
    END SpxWarning;

    PROCEDURE SpxError(spx : Spellix;
		       str : ARRAY OF CHAR);
      VAR tCh : CHAR;
    BEGIN
      StdError.WriteString("mpp: error: ");
      StdError.WriteString(str);
      IF spx <> emptySpx THEN
	StdError.WriteString(' <');
	MessageSpx(spx);
	StdError.WriteString('> ');
      ELSE StdError.Write(" ");
      END;
      WriteFilePos();
      StdError.WriteLn;
      errors := TRUE;
    END SpxError;

    PROCEDURE Message(spx : Spellix);
    BEGIN
      StdError.WriteString("mpp: ");
      IF spx <> emptySpx THEN
	MessageSpx(spx);
      END;
      StdError.WriteLn;
    END Message;

    PROCEDURE Read(VAR chr : CHAR);
    BEGIN
	ReadByte(input,chr);
       (*  On the pc, we must consume the cr of a cr-lf pair (cf InOut.Read),
        *  and also any ^Z at end of file (otherwise the ReadLn endfile logic
        *  fails, and the next GetSymbol loops looking for an 'interesting'
        *  character) *)
        IF chr = Ascii.cr THEN ReadByte(input,chr) END;
        IF chr = Ascii.sub THEN
          ReadByte(input,chr);
          IF NOT EndFile(input) THEN
            StdError.WriteString ("Embedded ^Z ignored!");
          END;
        END;
        IF chr = EOF THEN chr := "" END;
        IF chr = Ascii.lf THEN INC(line) END;
    END Read;

    PROCEDURE WriteRead(VAR chr : CHAR);
    BEGIN
        TextInOut.Write(output,chr);
	Read(chr);
    END WriteRead;

    PROCEDURE Write(chr : CHAR);
    BEGIN
      TextInOut.Write(output,chr);
    END Write;

  BEGIN
    line := 1;
    EnvironString("M2SYM",m2symPath);
  END InputOutput;
  (* ========================================== *)

  (* ========================================== *
   * This module supplies string table operations
   * and provided temporary storage for strings.
   * It initializes the table and enters the 
   * command symbol strings with predefined spix'
   * ========================================== *)
  MODULE StringTable;
    IMPORT Spellix, FatalError, Ascii, TextInOut, output;
    EXPORT Tide, Table, Copy, Mark, Reset, 
	StringsEqual, Compare, 
	SymEnter, SymExtract, Order,
	defSpx, undSpx, ifdSpx,	mesSpx,	errSpx,	(* symbol spix' *)
	ifnSpx, incSpx, elsSpx, endSpx,	ifsSpx,	(* symbol spix' *)
	debSpx0, hlpSpx0, debSpx1, hlpSpx1, 
        WriteSpix, ResetStringTable;

    TYPE Order = (less, equal, greater);

    VAR	defSpx, undSpx,  ifdSpx,  ifnSpx, 
	errSpx, debSpx0, debSpx1, elsSpx,  endSpx, 
	incSpx, mesSpx,  ifsSpx,  hlpSpx0, hlpSpx1 : Spellix;

    VAR table : ARRAY Spellix OF CHAR;
	tide  : Spellix;
	resetTide : Spellix;

    (* $I- *) (* $R- *) (* $S- overflow tests are explicit *)

    PROCEDURE Tide() : Spellix;
    BEGIN RETURN tide END Tide;

    PROCEDURE Table(spx : Spellix) : CHAR;
    BEGIN RETURN table[spx] END Table;

    PROCEDURE Copy(chr : CHAR);
    BEGIN table[tide] := chr; INC(tide) END Copy;

    PROCEDURE Reset(sp : Spellix);
    BEGIN tide := sp END Reset;

    PROCEDURE Mark();
    BEGIN
      IF tide > MAX(Spellix) THEN
	FatalError("string table overflow");
      ELSE table[tide] := ""; INC(tide);
      END;
    END Mark;

    PROCEDURE WriteSpix(spx : Spellix);
    BEGIN
      WHILE table[spx] <> "" DO
	TextInOut.Write(output,table[spx]);
	INC(spx);
      END;
    END WriteSpix;

    PROCEDURE StringsEqual(spx1, spx2 : Spellix) : BOOLEAN;
    BEGIN
      WHILE (table[spx1] = table[spx2]) AND 
	    (table[spx1] <> "") DO
	INC(spx1); INC(spx2);
      END;
      RETURN table[spx1] = table[spx2];
    END StringsEqual;

    PROCEDURE Compare(s1, s2 : Spellix) : Order;
      VAR c1, c2 : CHAR; (* Ascii collating sequence *)
    BEGIN
      c1 := table[s1];
      c2 := table[s2];
      WHILE (c1 = c2) AND (c2 # Ascii.nul) DO
	INC(s1); c1 := table[s1];
	INC(s2); c2 := table[s2];
      END;
      IF    c1 < c2 THEN RETURN less
      ELSIF c1 > c2 THEN RETURN greater
      ELSE (* c1 = c2 = Ascii.nul THEN *) RETURN equal
      END
    END Compare;
  
    PROCEDURE SymEnter(str : ARRAY OF CHAR;
		   VAR spx : Spellix);
      VAR index : Spellix;
    BEGIN
      spx := tide;
      index := 0;
      WHILE (index <= HIGH(str)) AND (str[index] <> "") DO
	table[tide] := str[index]; INC(tide); INC(index);
      END;
      table[tide] := ""; INC(tide);
    END SymEnter;

    PROCEDURE SymExtract(spx : Spellix;
		     VAR str : ARRAY OF CHAR);
      VAR index : CARDINAL;
    BEGIN
      index := 0;
      WHILE table[spx] <> "" DO
	str[index] := table[spx]; INC(spx); INC(index);
      END;
      str[index] := "";
    END SymExtract;

    PROCEDURE ResetStringTable();
    BEGIN
      tide := resetTide;
    END ResetStringTable;

  BEGIN
    table[0] := "";
    tide := 1;	(* tide = 0 is reserved *)
    SymEnter("define",  defSpx);
    SymEnter("undef",   undSpx);
    SymEnter("if",      ifsSpx);
    SymEnter("ifdef",   ifdSpx);
    SymEnter("ifndef",  ifnSpx);
    SymEnter("else",    elsSpx);
    SymEnter("endif",   endSpx);
    SymEnter("error",   errSpx);
    SymEnter("-debug",  debSpx0);
    SymEnter("-help",   hlpSpx0);
    SymEnter("/debug",  debSpx1);
    SymEnter("/help",   hlpSpx1);
    SymEnter("include", incSpx);
    SymEnter("message", mesSpx);
    resetTide := tide;
  END StringTable;
  (* $I= *) (* $R= *) (* $S= *)
  (* ========================================== *)
  
  (* ========================================== *)
  MODULE SymbolTable;
    FROM Storage IMPORT ALLOCATE, DEALLOCATE;
    IMPORT Spellix, Compare, Order, emptySpx, debug, DefNote;
    EXPORT Insert, Delete, Lookup, ResetTree;

  (*
   *  all the code here is borrowed from the
   *  module "cardtree.mod" from G&M's teachers
   *  manual and model answers
   *  Code has been changed to use Compare()
   *)

  TYPE Tree = POINTER TO TreeBlock;
       TreeBlock = RECORD
                     key   : Spellix;
		     subst : Spellix;
                     left, right : Tree;
                   END;

  VAR  tree : Tree;

  PROCEDURE Insert(key : Spellix; 
		   sub : Spellix;
		VAR ok : BOOLEAN);

    PROCEDURE RecInsert(VAR tre : Tree; element : Spellix);
    BEGIN
      IF tre = NIL THEN
        NEW(tre); 
	ok := TRUE;
        WITH tre^ DO
          key := element;
	  subst := sub;
	  left := NIL; right := NIL;
        END;
      ELSE
        CASE Compare(element, tre^.key) OF
        | less    : RecInsert(tre^.left,element);
        | greater : RecInsert(tre^.right,element);
        | equal   : tre^.subst := sub; 
		    ok := FALSE;
        END;
      END;
    END RecInsert;

  BEGIN
    RecInsert(tree,key);
    IF debug THEN DefNote(key,sub) END;
  END Insert;

  PROCEDURE Delete(key : Spellix; VAR ok : BOOLEAN);

    PROCEDURE RecDelete(VAR tre : Tree; element : Spellix);
      VAR remKey : Spellix; (* largest key in left subtree  *)
	  remSub : Spellix; (* subst of largest key in left *)
          savedTree : Tree; (* subtree of the disposed node *)

      PROCEDURE RemoveLargest(VAR t : Tree);
        VAR saved : Tree;
      BEGIN (* assert: t <> NIL *)
        IF t^.right <> NIL THEN RemoveLargest(t^.right);
        ELSE (* t^ is it! *)
          remKey := t^.key; (* the removed key *)
          saved := t^.left;
          DISPOSE(t);
          t := saved;
        END;
      END RemoveLargest;

    BEGIN
      IF tre = NIL THEN 
        ok := FALSE;
	RETURN 
      END;
      CASE Compare(element, tre^.key) OF
      | less    : RecDelete(tre^.left,element);
      | greater : RecDelete(tre^.right,element);
      | equal   : 
          IF tre^.left = NIL THEN
            savedTree := tre^.right;
            DISPOSE(tre);
            tre := savedTree;
          ELSIF tre^.right = NIL THEN
            savedTree := tre^.left;
            DISPOSE(tre);
            tre := savedTree;
          ELSE (* find and remove largest in left subtree *)
            RemoveLargest(tre^.left);
            tre^.key := remKey; (* copy to deleted node *)
	    tre^.subst := remSub;
          END;        
      END;
    END RecDelete;

  BEGIN
    ok := TRUE;
    RecDelete(tree,key);
  END Delete;

  PROCEDURE Lookup(element : Spellix) : Spellix;
    VAR temp : Tree;
  BEGIN (* iterative version *)
    temp := tree;
    WHILE temp <> NIL DO
      CASE Compare(element, temp^.key) OF
      | less    : temp := temp^.left;
      | greater : temp := temp^.right;
      | equal   : (* found *) RETURN temp^.subst;
      END;
    END;
    RETURN emptySpx;
  END Lookup;

  PROCEDURE ResetTree();
  BEGIN
    tree := NIL;
  END ResetTree;

  END SymbolTable;
  (* ========================================== *)
  
  (* ========================================== * 
   * There are two contexts in which the next
   * symbol is to be found: at start of line --
   * ReadLn, and elsewhere -- GetSymbol. This
   * difference is used to simplify the code.
   * There is also the case of scanning strings.
   * ========================================== *)
  MODULE Scanner;

    IMPORT SymbolType, Spellix, 		(* types        *)
	Write, WriteRead, Read, 		(* input-output *)
	Copy, Mark, Tide, Reset,		(* string table *)
	defSpx, undSpx, ifdSpx,	mesSpx,	errSpx,	(* symbol spix' *)
	ifnSpx, incSpx, elsSpx, endSpx,	ifsSpx,	(* symbol spix' *)
	StringsEqual, Table,			(* string table *)
	SpxWarning, SpxError, FatalError,	(* global utils *)
	EndFile, input, CloseAndRestore,
	IsLetter, Ascii, name, symbol, ch, emptySpx;

    EXPORT ReadLn, GetSymbol, GetExpSym,
	CopyRestOfLine, SkipTo, SkipRestOfLine, spix;

    TYPE CharSet = SET OF CHAR;

    VAR  spix : Spellix;

    CONST interestingChars = CharSet {"", "a" .. "z", "A" .. "Z", "\",
			     	 "0" .. "9", Ascii.lf, "(", "'", '"'};
	  identChars       = CharSet {"a" .. "z", "A" .. "Z",
					"_", "0" .. "9"};
	  numberChars      = CharSet {"0" .. "9", ".", "a" .. "f",
					"A" .. "F", "H"};

    PROCEDURE CopyRestOfLine();
    (* does not echo to output ever *)
    BEGIN
      spix := Tide();
      WHILE (ch = " ") OR (ch = Ascii.ht)  DO Read(ch) END;
      WHILE ch <> Ascii.lf DO 
        IF ch = "\" THEN
	  LOOP
	    Read(ch); (* ==> don't write it out *)
	    (*
	     *  if following character is not another "\"
	     *  then process it and look at the next.
	     *  If it is another "\" then ch is "\"
	     *)
            IF ch = "\" THEN (* "\\" *)
	      EXIT;
	    ELSE
	      Copy(ch); Read(ch);
	      IF ch <> "\" THEN EXIT END;
	    END;
	  END; (* loop *)
        END;
	Copy(ch); Read(ch);
      END;
      Read(ch); (* get past end of line char *)
      Mark();
      symbol := eol;
    END CopyRestOfLine;

    PROCEDURE SkipRestOfLine();
    BEGIN
      WHILE ch <> Ascii.lf DO Read(ch) END;
      Read(ch); (* get past end of line char *)
      symbol := eol;
    END SkipRestOfLine;

    PROCEDURE SkipTo(sym : SymbolType;
		     mes : ARRAY OF CHAR);
    BEGIN
      IF symbol <> sym THEN
	SpxError(emptySpx,mes);
      END;
      WHILE (symbol <> sym) AND
	    (symbol <> eof) DO GetSymbol(FALSE);
      END;
    END SkipTo;

    PROCEDURE GetSymbol(copy : BOOLEAN);
    (*
     *   get next symbol  --
     *     echo to output if copy = TRUE
     *
     *   Postcondition : ch is the next char following the symbol end
     *)

      VAR readP : PROCEDURE(VAR CHAR);
	  oldCh : CHAR;
	  depth : CARDINAL;
    BEGIN
      IF copy THEN readP := WriteRead ELSE readP := Read END;
      WHILE (ch = " ") OR (ch = Ascii.ht) DO readP(ch) END;
      IF ch = "\" THEN
	LOOP
	  Read(ch); (* ==> don't write it out *)
	  (*
	   *  if following character is not another "\"
	   *  then process it and look at the next.
	   *  If it is another "\" then ch is "\"
	   *)
          IF ch = "\" THEN (* "\\" *)
	    EXIT;
	  ELSE
	    readP(ch);
	    IF ch <> "\" THEN EXIT END;
	  END;
	END; (* loop *)
      END;
      IF ch = "" THEN symbol := eof;
      ELSIF IsLetter(ch) THEN (* identifier code *)
	spix := Tide();
	symbol := ident;
	Copy(ch);
	Read(ch); (* do not echo *)
	WHILE ch IN identChars DO 
	  Copy(ch);
	  Read(ch);
	END;
	Mark();
      ELSE (* some other symbol *)
	oldCh := ch;
	readP(ch); (* this writes out oldCh maybe ! *)
        CASE oldCh OF
        | Ascii.lf : symbol := eol;
	| "="      : symbol := equ;
	| "#"      : symbol := neq;
	| "<"      : 
	    IF ch = ">" THEN
	      symbol := neq; readP(ch);
	    ELSE
	      symbol := other;
	      WHILE NOT (ch IN interestingChars) DO readP(ch) END;
	    END;
        | '"', "'" : (* process literal string *)
	    WHILE (ch <> oldCh) AND (ch <> Ascii.lf) AND (ch <> "") DO
	      readP(ch);
	    END;
	 (*
	  *   this one is broken by "" !!! kjg Sep-92
	  *
	  * REPEAT readP(ch);
	  * UNTIL (ch = oldCh) OR (ch = Ascii.lf) OR (ch = ""); 
	  *)
	    readP(ch);
	    symbol := other;
        | "(" : (* skip over possibly nested comment *)
	    IF ch = "*" THEN
	      readP(ch);
	      depth := 1;
	      REPEAT
		IF ch = "" THEN 
		  FatalError("file ends in comment");
	        ELSIF ch = "*" THEN readP(ch);
	          IF ch = ")" THEN readP(ch); DEC(depth) END;
	        ELSIF ch = "(" THEN readP(ch);
		  IF ch = "*" THEN readP(ch); INC(depth) END;
	        ELSE readP(ch);
	        END;
	      UNTIL depth = 0; 
	      GetSymbol(copy);
	    ELSE
	      symbol := other;
	      WHILE NOT (ch IN interestingChars) DO readP(ch) END;
	    END;
	| "0" .. "9" : (* "number" -- don't stop too soon *)
	    symbol := other;
	    WHILE ch IN numberChars DO readP(ch) END;
	    WHILE NOT (ch IN interestingChars) DO readP(ch) END;
        ELSE (* "other" -- get max munch *)
	    symbol := other;
	    WHILE NOT (ch IN interestingChars) DO readP(ch) END;
        END; (* case *)
      END; (* elsepart *)
    END GetSymbol;

    PROCEDURE GetExpSym(VAR spx : Spellix);
    (*
     *   get next symbol from string, always echo
     *
     *   Postcondition : ch is the next char following the symbol end
     *)
     VAR  oldCh : CHAR;
	  depth : CARDINAL;

	PROCEDURE Rd(VAR cptr : Spellix);
	BEGIN
	  INC(cptr);
	  ch := Table(cptr);
	END Rd;

	PROCEDURE WrRd(VAR cptr : Spellix);
	BEGIN
	  Write(ch);
	  INC(cptr);
	  ch := Table(cptr);
	END WrRd;

    BEGIN
      WHILE (ch = " ") OR (ch = Ascii.ht) DO WrRd(spx) END;
      IF ch = "\" THEN
	LOOP
	  Rd(spx); (* ==> don't write it out *)
	  (*
	   *  if following character is not another "\"
	   *  then process it and look at the next.
	   *  If it is another "\" then ch is "\"
	   *)
          IF ch = "\" THEN (* "\\" *)
	    EXIT;
	  ELSE
	    WrRd(spx);
	    IF ch <> "\" THEN EXIT END;
	  END;
	END; (* loop *)
      END;
      IF ch = "" THEN symbol := eof;
      ELSIF IsLetter(ch) THEN (* identifier code *)
	spix := Tide();
	symbol := ident;
	Copy(ch);
	Rd(spx); (* do not echo *)
	WHILE ch IN identChars DO 
	  Copy(ch);
	  Rd(spx);
	END;
	Mark();
      ELSE (* some other symbol *)
	oldCh := ch;
	WrRd(spx); (* this writes out oldCh maybe ! *)
        CASE oldCh OF
        | Ascii.lf : symbol := eol;
        | '"', "'" : (* process literal string *)
  	    REPEAT WrRd(spx) 
	    UNTIL (ch = oldCh) OR (ch = Ascii.lf) OR (ch = ""); 
	    WrRd(spx);
	    symbol := other;
        | "(" : (* skip over possibly nested comment *)
	    IF ch = "*" THEN
	      WrRd(spx);
	      depth := 1;
	      REPEAT
		IF ch = "" THEN 
		  FatalError("expansion ends in comment");
	        ELSIF ch = "*" THEN WrRd(spx);
	          IF ch = ")" THEN WrRd(spx); DEC(depth) END;
	        ELSIF ch = "(" THEN WrRd(spx);
		  IF ch = "*" THEN WrRd(spx); INC(depth) END;
	        ELSE WrRd(spx);
	        END;
	      UNTIL depth = 0; 
	      GetExpSym(spx);
	    ELSE
	      symbol := other;
	      WHILE NOT (ch IN interestingChars) DO WrRd(spx) END;
	    END;
	| "0" .. "9" : (* "number" -- don't stop too soon *)
	    symbol := other;
	    WHILE ch IN numberChars DO WrRd(spx) END;
	    WHILE NOT (ch IN interestingChars) DO WrRd(spx) END;
        ELSE (* "other" -- get max munch *)
	    symbol := other;
	    WHILE NOT (ch IN interestingChars) DO WrRd(spx) END;
        END; (* case *)
      END; (* elsepart *)
    END GetExpSym;

    PROCEDURE ReadLn(copy : BOOLEAN);
    (*
     *   get next symbol after end of line --
     *     if a command, do not echo symbol to output
     *     if not a command, echo to output if copy = TRUE
     *)
      VAR   start : CHAR;
    BEGIN
      IF EndFile(input) THEN CloseAndRestore() END;
      IF ch <> "#" THEN GetSymbol(copy);
      ELSE (* else is command, ch = "#" *)
	REPEAT Read(ch) UNTIL (ch # " ") AND (ch # Ascii.ht);
	IF ch = Ascii.lf THEN 
	  symbol := bad;
	  SpxWarning(emptySpx,"bad command verb");
	ELSIF ch = "#" THEN (* a preprocessor comment *)
	  REPEAT Read(ch) UNTIL ch = Ascii.lf;
	  Read(ch); ReadLn(copy);
	ELSE (* probably a command *)
	  spix := Tide();
	  start := ch;
	  Copy(ch);
	  Read(ch); (* do not echo *)
	  WHILE IsLetter(ch) DO 
	    Copy(ch);
	    Read(ch);
	  END;
	  Mark();
	  IF (start = "d") AND StringsEqual(defSpx,spix) THEN 
	    symbol := define;
	  ELSIF (start = "u") AND StringsEqual(undSpx,spix) THEN 
	    symbol := undef;
	  ELSIF (start = "i") THEN
	    IF StringsEqual(ifsSpx,spix) THEN 
	      symbol := ifs;
	    ELSIF StringsEqual(ifdSpx,spix) THEN 
	      symbol := ifdef;
	    ELSIF StringsEqual(ifnSpx,spix) THEN 
	      symbol := ifndef;
	    ELSIF StringsEqual(incSpx,spix) THEN 
	      symbol := include;
	    ELSE symbol := bad;
	    END;
	  ELSIF (start = "e") THEN
	    IF StringsEqual(elsSpx,spix) THEN 
	      symbol := else;
	    ELSIF StringsEqual(endSpx,spix) THEN 
	      symbol := endif;
	    ELSIF StringsEqual(errSpx,spix) THEN 
	      symbol := error;
	    ELSE symbol := bad;
	    END;
	  ELSIF (start = "m") AND StringsEqual(mesSpx,spix) THEN 
	    symbol := message;
	  ELSE symbol := bad;
	  END;
	  IF symbol = bad THEN 
	    SpxWarning(spix,"bad command verb");
	  END;
	  Reset(spix);
	END;
      END; (* else is command *)
    END ReadLn;

  END Scanner;

  (* ========================================== *)

 (*
  *  This is a variant of the file name iterator in gpm-clr.
  *  In this case it iterates over a single argument with wildcards.
  *)
  MODULE FileNameIterator;

    IMPORT GetArg, SYSTEM, Wildcards;
    EXPORT InitIterator, GetNextArg, hasWildcards;

   (*
    *  This is a typical Modula-2 hack.
    *  We define a type "pointer to a fixed length array" and
    *  then assign a "pointer to an arbitrary length array"
    *  to the variable.  We may then index into the array
    *  with bounds checks turned off, relying on the fact 
    *  that the final pointer in the UxArgBlock will be NIL.
    *)
    TYPE ChArrayPtr = POINTER TO ARRAY [0 .. 7] OF CHAR;
    TYPE UxArgBlock = POINTER TO ARRAY [0 .. 7] OF ChArrayPtr;

    VAR  argNum : CARDINAL;
         argPtr : UxArgBlock;
         argIdx : CARDINAL;
         argTmp : ARRAY [0 .. 127] OF CHAR;

    PROCEDURE hasWildcards(VAR str : ARRAY OF CHAR) : BOOLEAN;
      VAR idx : CARDINAL;
          chr : CHAR;
    BEGIN
      FOR idx := 0 TO HIGH(str) DO
        chr := str[idx];
        IF chr = "*" THEN RETURN TRUE;
        ELSIF chr = "" THEN RETURN FALSE;
        END;
      END;
      RETURN FALSE;
    END hasWildcards;

    PROCEDURE InitIterator(idx : CARDINAL);
    BEGIN
      argNum := idx;
      argPtr := NIL;
    END InitIterator;

(* $I- Turn off index bounds checks *)
(* $R- Turn off range bounds checks *)

    PROCEDURE GetNextArg(VAR arg : ARRAY OF CHAR; VAR ok : BOOLEAN);
      (* ---- *)
      PROCEDURE AssignP(VAR s : ARRAY OF CHAR; p : ChArrayPtr);
        VAR i : CARDINAL;
            c : CHAR;
      BEGIN
        REPEAT
          c := p^[i]; s[i] := c; INC(i);
        UNTIL (c = "") OR (i > HIGH(s));
      END AssignP;
      (* ---- *)
      VAR strPtr : ChArrayPtr;
    BEGIN
     (*
      *  First: check if we are inside a wildcard iteration
      *)
      IF argPtr = NIL THEN
       (*
        *  If so, then initialize another iteration
        *  and then fall through to following code.
        *)
        GetArg(argNum, argTmp);
        argPtr := SYSTEM.CAST(UxArgBlock, 
                        Wildcards.GetMatchingFiles(".", argTmp));
        argIdx := 0;
      END;
      ok := FALSE;
      IF argPtr # NIL THEN
       (*
        *  We are inside a wildcard iteration.
        *  Check if there are arguments left.
        *)
        strPtr := argPtr^[argIdx]; INC(argIdx);
        IF strPtr # NIL THEN
         (*
          *  Yes there are args left.  Return the next one.
          *)
          AssignP(arg, strPtr); ok := TRUE; 
        END;
      END;
    END GetNextArg;

(* $I= *)
(* $R= *)
  BEGIN
    argPtr := NIL;
  END FileNameIterator;

  (* ========================================== * 
   *   This is the main parser of the processor
   *   The code is a simple recursive descent
   *   parser for the following grammar ---
   *
   *	      goal -> program eof.
   *	   program -> {line}.
   *	      line -> command | {token} eol.
   *	   command -> ## {any_non_eol} eol	-- mpp comment
   *		   |  #message restOfLine eol
   *		   |  #define ident restOfLine eol
   *		   |  #undef ident eol
   *		   |  #include restOfLine eol
   *		   |  #error eol
   *		   |  #if ident (= | <> | #) restOfLine eol {line}
   *			[#else ident eol {line}] #endif ident eol
   *		   |  #ifdef ident eol {line}
   *			[#else ident eol {line}] #endif ident eol
   *		   |  #ifndef ident eol {line}
   *			[#else ident eol {line}] #endif ident eol.
   *	restOfLine -> "any string not including end of line".
   *
   *   The alphabet is --
   *	(eof, eol, other_token, ident, #define, #message, #error,
   *	 #include, #undef, #if, #ifdef, #ifndef, #else, #endif,
   *	 equ, neq)
   *
   * ========================================== *)

  CONST maxDepth = 32;
  VAR   recDepth : CARDINAL; (* check recursion depth *)

  PROCEDURE Note(s1, s2 : Spellix; cond : BOOLEAN);
  BEGIN
    WriteFilePos();
    IF cond THEN StdError.WriteString(" equal(");
    ELSE StdError.WriteString(" unequal(");
    END;
    MessageSpx(s1);
    StdError.Write(",");
    MessageSpx(s2);
    StdError.WriteString(") ==> ");
    IF StringsEqual(s1,s2) <> cond THEN 
      StdError.WriteString("FALSE");
    ELSE StdError.WriteString("TRUE");
    END;
    StdError.WriteLn;
  END Note;

  PROCEDURE DefNote(s1, s2 : Spellix);
  BEGIN
    WriteFilePos();
    StdError.WriteString("def-subst: ");
    MessageSpx(s1);
    StdError.WriteString(' = "');
    MessageSpx(s2);
    StdError.Write('"');
    StdError.WriteLn;
  END DefNote;

  PROCEDURE Check(s1 : Spellix; cond : BOOLEAN);
  BEGIN
    WriteFilePos();
    IF cond THEN StdError.WriteString(" defined(");
    ELSE StdError.WriteString(" undefined(");
    END;
    MessageSpx(s1);
    IF (Lookup(s1) <> emptySpx) <> cond THEN 
      StdError.WriteString(") ==> FALSE");
    ELSE StdError.WriteString(") ==> TRUE");
    END;
    StdError.WriteLn;
  END Check;

  PROCEDURE LineSequence(copy : BOOLEAN);
    CONST followLineSeq = SymbolSet{else, endif, eof};
    VAR   idSpx : Spellix;
	  rpSpx : Spellix;
	  openOk : BOOLEAN;

      PROCEDURE Conditional(sym : SymbolType);
	VAR idSpx : Spellix;
	    subst : Spellix; (* substitution of ident *)
	    match : BOOLEAN; (* ==> condition was met *)
	    equSy : BOOLEAN; (* ==> relop was "equal" *)
      BEGIN
	GetSymbol(FALSE);
	idSpx := spix;
	IF symbol <> ident THEN 
	  SpxError(emptySpx,"ident must follow if, ifdef, ifndef");
	ELSE
	  CASE sym OF
	  | ifs    :
	      GetSymbol(FALSE);  (* get past ident *)
	      IF (symbol = equ) OR (symbol = neq) THEN
		equSy := symbol = equ;
	      ELSE SpxError(emptySpx,"only '=', '<>' allowed here");
	      END;
	      CopyRestOfLine();
	      subst := Lookup(idSpx);
	      IF debug THEN 
		IF subst <> emptySpx THEN Note(subst,spix,equSy);
		ELSE Check(idSpx,equSy);
	        END;
	      END;
	      match := equSy =
			((subst <> emptySpx) AND StringsEqual(subst,spix));
	      Reset(spix);
	  | ifdef  :
	      SkipRestOfLine();  (* should be empty ... *)
	      IF debug THEN Check(idSpx,TRUE) END;
	      match := (Lookup(idSpx) <> emptySpx);
	  | ifndef :
	      SkipRestOfLine();  (* should be empty ... *)
	      IF debug THEN Check(idSpx,FALSE) END;
	      match := (Lookup(idSpx) = emptySpx);
	  END; (* case sym of *)

	  ReadLn(match AND copy);
	  LineSequence(match AND copy);
	  IF symbol = else THEN
	    GetSymbol(FALSE);
	    IF (symbol <> ident) OR
		NOT StringsEqual(spix,idSpx) THEN 
	      IF debug THEN Note(spix,idSpx,TRUE) END;
	      SpxError(idSpx,"after else, should be");
	    ELSE Reset(spix);
	    END;
	    SkipRestOfLine();  (* should be empty ... *)
	    ReadLn(NOT match AND copy);
	    LineSequence(NOT match AND copy);
	  END;
	  SkipTo(endif,"expected endif symbol");
	  GetSymbol(FALSE);
	  IF (symbol <> ident) OR
	      NOT StringsEqual(spix,idSpx) THEN 
	    IF debug THEN Note(spix,idSpx,TRUE) END;
	    SpxError(idSpx,"after endif, should be");
	  ELSE Reset(spix);
	  END;
	  SkipRestOfLine();  (* should be empty ... *)
	  ReadLn(copy);
        END;
      END Conditional;

  BEGIN
        WHILE NOT (symbol IN followLineSeq) DO
        (* pre : previous fetch was ReadLn *)
  	  CASE symbol OF
	  | ifs, ifdef, ifndef : Conditional(symbol);
	  | define :
	      GetSymbol(FALSE);
	      idSpx := spix;
	      IF symbol <> ident THEN 
	        SpxError(emptySpx,"define must be followed by identifier");
	        SkipRestOfLine();
	      ELSIF copy THEN
	        CopyRestOfLine();
	        Insert(idSpx,spix,ok);
	        IF NOT ok THEN
	          SpxWarning(idSpx,"overwrite of definition");
	        END;
	      ELSE 
		SkipRestOfLine();
	      END;
	      ReadLn(copy);
	  | undef :
	      GetSymbol(FALSE);
	      idSpx := spix;
	      IF symbol <> ident THEN 
	        SpxError(emptySpx,"undef must be followed by identifier");
	        SkipRestOfLine();
	      ELSIF copy THEN
	        SkipRestOfLine();  (* should be empty ... *)
	        Delete(idSpx,ok);
	        IF NOT ok THEN
	          SpxWarning(idSpx,"undef of unknown symbol");
	        END;
	      ELSE SkipRestOfLine();
	      END;
	      ReadLn(copy);
	  | error :
	      IF copy THEN SpxError(emptySpx,"#error called") END;
	      SkipRestOfLine();
	      ReadLn(copy);
	  | message :
	      IF copy THEN
	        CopyRestOfLine();
		Message(spix);
		Reset(spix);
	      ELSE SkipRestOfLine();
	      END;
              ReadLn(copy);
	  | include :
	      IF copy THEN
	        CopyRestOfLine();
	        SaveAndOpen(spix,TRUE,openOk);
	        IF openOk THEN Read(ch);
	        ELSE SpxError(spix,"can't find include file");
	        END;
	      ELSE SkipRestOfLine();
	      END;
              ReadLn(copy);
	  ELSE (* other line *)
	    WHILE symbol > eol DO
	      IF (symbol = ident) AND copy THEN 
	        idSpx := Lookup(spix);
	        IF copy AND (idSpx <> emptySpx) THEN
		  recDepth := 0;
	  	  ProcessExpansion(idSpx);
	        ELSE WriteSpix(spix);
	        END;
	        Reset(spix);
	      END;
	      GetSymbol(copy);
	    END;
	    IF symbol = eol THEN ReadLn(copy) END;
	  END; (* case *)
        (* post : eol has been read past *)
        END; (* while *)
  END LineSequence;

  PROCEDURE ProcessExpansion(spell : Spellix);
    VAR savCh : CHAR; (* the saved "next" character *)
	expSp : Spellix;
  BEGIN
    INC(recDepth);
    IF recDepth > maxDepth THEN
      SpxError(spell,"apparently recursive expansion");
      RETURN;
    END;
    savCh := ch;
    ch := Table(spell);
    GetExpSym(spell);
    WHILE symbol <> eof DO
      IF symbol = ident THEN (* spix is a new copy *)
	expSp := Lookup(spix);
	IF expSp <> emptySpx THEN
	  ProcessExpansion(expSp);
	ELSE 
	  WriteSpix(spix);
	END;
	Reset(spix);	     (* so remove it now *)
      END;
      GetExpSym(spell);
    END; (* while *)
    ch := savCh;
  END ProcessExpansion;

  PROCEDURE MacroProcessFile();
  BEGIN
    IF errors THEN RETURN END;
    ReadLn(TRUE);
    LineSequence(TRUE);
    IF symbol <> eof THEN
      SpxError(emptySpx,"expected end of file");
      WHILE symbol <> eof DO GetSymbol(FALSE) END;
    END;
    UxFiles.Close(output,ok);
  END MacroProcessFile;

  (* ========================================== * 
   *   Various utilities for mainline code
   * ========================================== *)
  PROCEDURE Define(arg : ARRAY OF CHAR);
    VAR sSpx, rSpx : Spellix;
	argIx : CARDINAL;
	this  : CHAR;
        ok    : BOOLEAN;
  BEGIN
    argIx := 2;
    sSpx := Tide();
    this := arg[argIx]; INC(argIx);
    WHILE (this <> "=") AND (this <> "") DO
      Copy(this);
      this := arg[argIx]; INC(argIx);
    END;
    Mark();
    rSpx := Tide();
    IF this <> "" THEN
      this := arg[argIx]; INC(argIx);
      WHILE this <> "" DO
        Copy(this);
        this := arg[argIx]; INC(argIx);
      END;
    END;
    Mark();
    Insert(sSpx,rSpx,ok);
    IF NOT ok THEN
      SpxWarning(sSpx,"overwrite of definition");
    END;
  END Define;

  PROCEDURE UnDefine(arg : ARRAY OF CHAR);
    VAR sSpx  : Spellix;
	argIx : CARDINAL;
	this  : CHAR;
        ok    : BOOLEAN;
  BEGIN
    argIx := 2;
    sSpx := Tide();
    this := arg[argIx]; INC(argIx);
    WHILE this <> "" DO
      Copy(this);
      this := arg[argIx]; INC(argIx);
    END;
    Mark();
    Delete(sSpx,ok);
    IF NOT ok THEN
      SpxWarning(sSpx,"undef of unknown symbol");
    END;
  END UnDefine;

  PROCEDURE MakeOutName(VAR inoutName : ARRAY OF CHAR);
    VAR index : CARDINAL;
  BEGIN
    index := 0;
    WHILE inoutName[index] <> "" DO INC(index) END;
    IF (inoutName[index - 1] = "p") AND
       (inoutName[index - 2] = "p") THEN
      IF (inoutName[index - 3] = "m") THEN
	inoutName[index - 2] := "o";
	inoutName[index - 1] := "d";
      ELSIF (inoutName[index - 3] = "d") THEN
	inoutName[index - 2] := "e";
	inoutName[index - 1] := "f";
      ELSE SpxError(emptySpx,"unknown file extension");
      END;
    ELSE SpxError(emptySpx,"unknown file extension");
    END;
  END MakeOutName;

  VAR index  : CARDINAL;
      argC   : CARDINAL;
      ok     : BOOLEAN;
      badSpx : Spellix;
      modTim : CARDINAL;
      optSeq : Sequence;
      arg, outArg : ARRAY [0 .. 255] OF CHAR;

  PROCEDURE DoOptions(seq : Sequence; tim : CARDINAL);
    CONST line1 = " * =========== macro processed output from MPP  ==========";
          line2 = " * =======================================================";
    VAR curs : ElemPtr;
	elem : CARDINAL;
        opt  : ARRAY [0 .. 255] OF CHAR;
        presTimStruct, modTimStruct : SysClock.DateTime;
        timeString : ARRAY [0 .. 21] OF CHAR;


    PROCEDURE WriteBlankCommentLine;
    BEGIN
      TextInOut.WriteString(output," *"); 
      TextInOut.WriteLn(output);
    END WriteBlankCommentLine;

  BEGIN
    TextInOut.WriteString(output,"(*"); 
    TextInOut.WriteLn(output);
    TextInOut.WriteString(output,line1); 
    TextInOut.WriteLn(output);
    WriteBlankCommentLine;
    TextInOut.WriteString(output," * input file  : "); 
    TextInOut.WriteString(output,arg); 
    TextInOut.WriteLn(output);
    TextInOut.WriteString(output," * time stamp  : ");
(* infile modify time ... *)
    AsciiTime.TimeToStructTime(modTim,modTimStruct);
    AsciiTime.StructTimeToAscii(timeString,modTimStruct);
    TextInOut.WriteString(output,timeString);
(* end modify time    ... *)
    TextInOut.WriteLn(output);
    WriteBlankCommentLine;
    TextInOut.WriteString(output," * output file : "); 
    TextInOut.WriteString(output,outArg); 
    TextInOut.WriteLn(output);
    TextInOut.WriteString(output," * created at  : "); 
(* current time ... *)
    SysClock.GetClock(presTimStruct);
    AsciiTime.StructTimeToAscii(timeString,presTimStruct);
    TextInOut.WriteString(output,timeString);
(* end current time ... *)
    TextInOut.WriteLn(output);
    WriteBlankCommentLine;
    TextInOut.WriteString(output," * options ... : "); 
    InitCursor(seq,curs);
    WHILE NOT Ended(curs) DO
      GetNext(curs,elem);
      GetArg(elem,opt);
      TextInOut.Write(output," "); 
      TextInOut.WriteString(output,opt); 
      IF opt[1] = "D" THEN Define(opt) ELSE UnDefine(opt) END;
    END;
    TextInOut.WriteLn(output);
    WriteBlankCommentLine;
    TextInOut.WriteString(output,line2); 
    TextInOut.WriteLn(output);
    TextInOut.WriteString(output," *)"); 
    TextInOut.WriteLn(output);
    TextInOut.WriteLn(output);
  END DoOptions;

  PROCEDURE DoHelp;
  BEGIN
    StdError.WriteLn; StdError.WriteString(
    "Usage : mpp {[options] file}");
    StdError.WriteLn; StdError.WriteString(
'   Option   -> Define | Undefine | "/debug" | "/help"');
    StdError.WriteLn; StdError.WriteString(
'   Define   -> "/D"SymOrSub       // Define symbol or define substitution');
    StdError.WriteLn; StdError.WriteString(
'   SymOrSub -> symbol             // Symbol is any Modula-2 identifier');
    StdError.WriteLn; StdError.WriteString(
'                                  // Symbol is now defined for #ifdef etc.');
    StdError.WriteLn; StdError.WriteString(
'             | symbol"="string    // String is substitution for symbol');
    StdError.WriteLn; StdError.WriteString(
'   Undefine -> "/U"symbol         // Symbol is now undefined for #ifdef etc.');
    StdError.WriteLn; StdError.WriteString(
'   Unix-style option prefix "-" is also permitted'); 
    StdError.WriteLn; StdError.WriteString(
    'Options do not have spaces between the key (D|U) and the symbol,');
    StdError.WriteLn; StdError.WriteString(
    'or on either side of the optional equals sign. The string does not need');
    StdError.WriteLn; StdError.WriteString(
    'to be quoted if it is a single token for the command line processer.');
    StdError.WriteLn;
  END DoHelp;

  PROCEDURE ProcessFile(VAR fNm : ARRAY OF CHAR);
    VAR ok : BOOLEAN;
  BEGIN
    InitializeInputStack();
    ResetTree();                 (* clear all tables, then  *)
    ResetStringTable();          (* process the accumulated *)
    SymEnter(fNm,spix);
    SaveAndOpen(spix,FALSE,ok);
    IF ok THEN 
     (*
      *  now process the individual file
      *)
      errors := FALSE;
      ModifyTime(fNm,modTim,ok);
      MakeOutName(outArg);
      Read(ch);
      IF NOT errors THEN 
        UxFiles.Create(output,outArg,ok);
        IF NOT ok THEN
          SymEnter(outArg,badSpx);
          SpxError(badSpx,"cannot create");
        ELSE
          IF announce THEN 
            InOut.WriteString(fNm); InOut.WriteLn;
          END;                           (* process the accumulated *)
          DoOptions(optSeq,modTim);      (* command line options,   *)
          MacroProcessFile();            (* then the actual file... *)
          IF errors THEN UxFiles.Delete(outArg,ok) END;
        END;
      END;
    ELSE 
      SymEnter(fNm,badSpx);
      SpxError(badSpx,"file not found");
    END; (* else not found *)
  END ProcessFile;

  VAR argMin : CARDINAL;
      valid  : BOOLEAN;

BEGIN
  debug := FALSE;
  announce := FALSE;			(* this is never cleared *)
  argC  := ArgNumber();
  argMin := 0;
  (*
   *  check for valid command args
   *)
  IF argC = argMin THEN 
    StdError.WriteString("usage : mpp {[options] file}"); StdError.WriteLn;
    StdError.WriteString('option: "/D"<symbol>["="<string>]'); StdError.WriteLn;
    StdError.WriteString('option: "/U"<symbol>'); StdError.WriteLn;
    StdError.WriteString('option: "/debug" | "/help"'); StdError.WriteLn;
    HALT;
  END;
  (*
   *  now scan the arg list, saving all option 
   *  indices and processing non-options as files
   *)
  InitSequence(optSeq);
  FOR index := argMin TO argC - 1 DO
    GetArg(index,arg);
    IF (arg[0] = "-") OR (arg[0] = "/") THEN 
      IF (arg[1] = "D") OR (arg[1] = "U") THEN 
	(* accumulate options so far *)
	LinkRight(optSeq,index);
      ELSE
        spix := Tide();
        SymEnter(arg,badSpx);
	IF    StringsEqual(badSpx,debSpx0) OR 
	      StringsEqual(badSpx,debSpx1) THEN 
	  debug := TRUE;
	ELSIF StringsEqual(badSpx,hlpSpx0) OR 
	      StringsEqual(badSpx,hlpSpx1) THEN 
          DoHelp;
	ELSE
          SpxWarning(badSpx,"bad option");
	END;
      END;
    ELSE (* should be file ... *)
      outArg := arg;
      IF (index < argC - 1) OR hasWildcards(arg) THEN  
	announce := TRUE;	(* set the sticky flag ... *)
      END; 			
      InitIterator(index);
      LOOP 
        GetNextArg(arg, valid);
        IF NOT valid THEN EXIT END;
        outArg := arg;
        ProcessFile(arg);
      END; (* of LOOP *)
    END; (* else not option *)
  END; (* for args *)
END MPP.
