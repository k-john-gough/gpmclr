(*
 * =========== macro processed output from MPP  ==========
 *
 * input file  : mknameha.mpp
 * time stamp  : 2004:01:09::10:56:50
 *
 * output file : mknameha.mod
 * created at  : 2004:01:12::14:21:43
 *
 * options ... :  /Ddotnet86
 *
 * =======================================================
 *)

(* -- RCS header --
	$Log:	mknameha.mpp,v $
Revision 1.3  94/01/14  10:49:35  mboss
Added Windows NT changes.

Revision 1.2  93/11/03  09:01:15  mboss
Added DEC Alpha changes.

Revision 1.1  93/03/25  14:31:57  mboss
Initial revision

*)
(* 
 *  extracted with 
 * 	    "opsys" == "windows"
 * 	   "endian" == "little"
 *	"processor" == "iap386"
 *)


(****************************************************************)
(*                                                              *)
(*              Modula-2 Compiler Source Module                 *)
(*                                                              *)
(*           Name-handling for the lexical scanner.             *)
(*       Contains nested string and hash table modules.         *)
(*                                                              *)
(*           (c) copyright 1987 SoftWare Automata.              *)
(*                                                              *)
(*      original module : kjg july 1987                         *)
(*      modifications   : Version with alternative              *)
(*                        res-word handling.      kjg  7-aug-87 *)
(*                      : new res-words NIL, REM  kjg 15-Feb-88 *)
(*                      : 16-Mar-88                             *)
(*			: 03-Nov-88 more careful use of Commit  *)
(*			: 27-May-89 used bucket ADT		*)
(*			: 14-Jul-91 InitExcl. not used for pc   *)
(*                                                              *)
(*               CUT DOWN VERSION FOR PC GPMAKE                 *)
(*                     dwc September 1991                       *)
(*								*)
(*			: 20-Mar-92 kjg mods for decode as well	*)
(*			: 30-Apr-92 jrh increase stringTableMax *)
(*			:	        add Summary cf m2nameha *)
(*                      : kjg 03-Aug-92 uses new GpFiles procs  *)
(*                              and delete Shorten and Lower    *)
(*                      : pms 14-Jan-94 Added Windows NT version*)
(*								*)
(****************************************************************)




IMPLEMENTATION MODULE MkNameHandler;

(*      +---------------------------------------+
        |  MODULE M2NameHandler                 |
        |   +-------------------------------+   |
        |   |  MODULE Strings               |   |
        |   +-------------------------------+   |
        |   +-------------------------------+   |
        |   |  MODULE HashTable             |   |
        |   +-------------------------------+   |
        +---------------------------------------+              *)

FROM SYSTEM IMPORT CAST;
FROM Storage IMPORT ALLOCATE, DEALLOCATE;
FROM MkAlphabets IMPORT Spellix, HashBucketType, TermSymbols,
			FileNameType;
FROM MkInOut IMPORT AbortMessage;
FROM UxFiles IMPORT File, Close;
FROM Ascii IMPORT nul;
FROM GpFiles IMPORT GpFindLocal, GpFindOnPath;
FROM StdError IMPORT Write, WriteString, WriteLn, WriteCard; (* interim *)

  CONST entryMax = 5987; (* 3571 *) (* number of entries in Hash table *)
                        (* this MUST be a prime number.    *)
                        (* value made smaller for pc version *)
        stringTableMax = MAX(Spellix); (* = 65535 at 30 Apr 92 *)
			(* increased from 36 * 1024 for IBM Lang & Comp Dev *)
                        (* size of string table *)
                        (* maybe about 6 * entryMax ?? or 10 for IBM *)
        oldFileNameLength = 8;

  PROCEDURE Summary();
  BEGIN
    StringSummary();
    HashSummary();
  END Summary;

(****************************************************************)

MODULE Strings;

  IMPORT Spellix, entryMax, stringTableMax, TermSymbols,
         SpellingIndex, HashBucketType, (*Error,*) AbortMessage;

  IMPORT Write, WriteString, WriteCard, WriteLn,
         (* only needed for summary *)
         nul, File, FileNameType, CAST,
         GpFindLocal, GpFindOnPath, Close;

  EXPORT GetSourceRep, StringsEqual, StringSummary, StringTable,
         MarkInterimSpellix, InterimSpellix, Purge, empty,
         MarkEnd, WordEnter, ResWordEnter, ResSymbol, 
         SetLimit, CopyChar, CopyAndHash, HashCurrentId,
         (* set operations *)
         Commit, MakeFileName, FindFileName, FindFileNameOnPath;

  CONST ovrflo = "Error: String table overflow";

  VAR   table : ARRAY[1 .. stringTableMax] OF CHAR;
        (* A Spellix is actually an index into this array *)

  VAR   interim  : Spellix;
        empty    : Spellix;  (* an illegal entry *)
        tide     : Spellix;
        tStart   : Spellix;  (* start of temporaries *)
        limit    : Spellix;  (* this is the highTide mark after
                                all reserved word insertions *)
(*
 *      limit2   : Spellix;  (* this is the highTide mark after
 *                              C key words and other reserved
 *                              words have been entered      *)
 *)

  VAR   hashTotal : CARDINAL;

        PROCEDURE StringTable(spix : Spellix) : CHAR;
 	BEGIN  (* put back in kjg Mar-92 *)
	  RETURN table[spix];
	END StringTable;

        (**************************************************)
        (* some reserved word handling utility procedures *)
        (**************************************************)

        PROCEDURE ResWordEnter(str : ARRAY OF CHAR;
                               sym : TermSymbols);
          VAR ix : CARDINAL; (* index into string  *)
        BEGIN
          table[tide] := CHR(ORD(sym));
          INC(tide);
          MarkInterimSpellix;
          FOR ix := 0 TO HIGH(str) DO
            IF str[ix] <> nul THEN
              CopyAndHash(str[ix]);
            END;
          END;
          MarkEnd();
        END ResWordEnter;

        PROCEDURE ResSymbol(sp : Spellix) : TermSymbols;
        BEGIN
          IF sp < limit THEN
            RETURN VAL(TermSymbols,ORD(table[sp - 1]));
          ELSE RETURN ident
          END;
        END ResSymbol;

        PROCEDURE SetLimit;
        BEGIN
          limit := tide;
        END SetLimit;

(*
 *      PROCEDURE SetLimit2;
 *      BEGIN
 *        limit2 := tide;
 *      END SetLimit2;
 *)

        PROCEDURE WordEnter(str : ARRAY OF CHAR);
          VAR ix : CARDINAL; (* index into string  *)
              ch : CHAR;
        BEGIN
          MarkInterimSpellix;
          ix := 0; ch := str[ix];
          LOOP
            IF ch = nul THEN EXIT END;
            CopyAndHash(ch);
            IF ix = HIGH(str) THEN EXIT END;
            INC(ix); ch := str[ix];
          END;
          MarkEnd();
        END WordEnter;

(*$R-*) (*$I-*) (*$S-*) (*$T-*)
        PROCEDURE Commit();
        BEGIN
          tStart := tide;
        END Commit;
	
(*$R=*) (*$I=*) (*$S=*) (*$T=*)

        (**************************************************)
(****************** back in module Strings **********************)

  PROCEDURE GetSourceRep(ident : HashBucketType;
                         VAR str : ARRAY OF CHAR;
                         VAR idx : CARDINAL);
  (* precondition  : 0 <= idx <= HIGH(str); N.B. idx is <INOUT>
     postcondition : the string at spix"^" is copied from
                     str[pre-idx] to str[idx - 1]. str[idx] is
                     SYSTEM.TermChar. If str is too short,
                     string is truncated.                        *)
    VAR spix : Spellix;
  BEGIN
    IF ident >= entryMax THEN spix := empty;
    ELSE spix := SpellingIndex(ident);
    END;
(*
 *  IF spix < limit2 THEN
 *    str[idx] := "_"; INC(idx);
 *  END;
 *)
    WHILE (idx < HIGH(str)) AND (table[spix] <> nul) DO
      str[idx] := table[spix];
      INC(idx); INC(spix);
    END;
    str[idx] := nul;
  END GetSourceRep;

(* ============================================================ *)
  TYPE   ExtStringTable = ARRAY FileNameType OF
                            ARRAY [0 .. 3] OF CHAR;
  CONST  extTable = ExtStringTable{
                        "def",  (* def *)
                        "mod",  (* mod *)
                        "syx",  (* syx *)
                        "rfx",  (* rfx *)
                        "dll",  (* obj *)       (* CLR *)
                        "mak",  (* mak *)
                        "bat",  (* bat *)       (* PC *)
                        "exe"}; (* exe *)       (* W32 *)
(* ============================================================ *)

  PROCEDURE MakeFileName (hsh   : HashBucketType;
                          fType : FileNameType;
                      VAR fName : ARRAY OF CHAR);
  VAR
    index, jndex : CARDINAL;
    ch : CHAR;
  BEGIN
    index := 0;
    jndex := 0;
   (*
    *  Special code for Windows/CLR version only
    *)
    IF fType = bat THEN
      fName[0] := "M"; fName[1] := "k"; fName[2] := "-"; index := 3;
    END;
    GetSourceRep(hsh,fName,index);
    ch := extTable[fType][0];
    IF ch <> "" THEN
      fName[index] := "."; INC(index);
      REPEAT
        fName[index] := ch;
        INC(jndex); INC(index);
        ch := extTable[fType][jndex];
      UNTIL ch = "";
    END;
    fName[index] := "";
  END MakeFileName;

  PROCEDURE FindFileName (nam : HashBucketType;
                          ext : FileNameType;
                      VAR out : ARRAY OF CHAR;
                      VAR found : BOOLEAN);
    VAR file  : File;
        ok    : BOOLEAN;
        index : CARDINAL;
  BEGIN
    index := 0;
    GetSourceRep(nam,out,index);
    GpFindLocal(out,extTable[ext],out,file);
    found := file <> NIL;
    IF found THEN Close(file,ok) END;
  END FindFileName;

  PROCEDURE FindFileNameOnPath 
			 (nam   : HashBucketType;
                          ext   : FileNameType;
			  path  : ARRAY OF CHAR;
                      VAR out   : ARRAY OF CHAR;
                      VAR found : BOOLEAN);
    VAR file  : File;
        ok    : BOOLEAN;
        index : CARDINAL;
  BEGIN
    index := 0;
    GetSourceRep(nam,out,index);
    GpFindOnPath(path,out,extTable[ext],out,file);
    found := file <> NIL;
    IF found THEN Close(file,ok) END;
  END FindFileNameOnPath;

(*$R-*) (*$I-*) (*$S-*) (*$T-*)

  PROCEDURE StringsEqual(s1, s2 : Spellix) : BOOLEAN;
  BEGIN
    WHILE (table[s1] = table[s2]) AND
          (table[s1] <> nul) DO
      INC(s1); INC(s2);
    END;
    RETURN table[s1] = table[s2]
  END StringsEqual;
(*$R=*) (*$I=*) (*$S=*) (*$T=*)

  PROCEDURE MarkInterimSpellix;
  (* postcondition : interim is the spelling index of any
                     string subsequently entered                *)
  BEGIN
    interim := tide;
    hashTotal := 0;
  END MarkInterimSpellix;

  PROCEDURE InterimSpellix() : Spellix;
  BEGIN
    RETURN interim;
  END InterimSpellix;

(*$R-*) (*$I-*) (*$S-*) (*$T-*)
  PROCEDURE CopyChar(ch : CHAR);
  (* postcondition : ch is added to end of current interim string *)
  BEGIN
    table[tide] := ch;
    INC(tide);
  END CopyChar;

  PROCEDURE CopyAndHash(ch : CHAR);
  (* postcondition : ch is added to end of current interim string *)
    VAR msb : BOOLEAN;
  BEGIN
    table[tide] := ch;
    INC(tide);
    (* rotate hashTotal *)
    msb := CAST(INTEGER,hashTotal) < 0;
    hashTotal := hashTotal * 2 + ORD(ch) + ORD(msb);
  END CopyAndHash;

  PROCEDURE MarkEnd();
  (* postcondition : String is terminated by the
                     reserved value SYSTEM.TermChar		*)
  BEGIN
    table[tide] := nul;
    IF tide >= stringTableMax THEN
      AbortMessage(ovrflo,"");
    END;
    INC(tide);
  END MarkEnd;
(*$R=*) (*$I=*) (*$S=*) (*$T=*)


  PROCEDURE Purge();
  (* postcondition : the interim string is discarded. The high-
                     tide mark of the table is cut back to the 
                     last MarkInterimSpellix value.                *)
  BEGIN
    tide := interim;
  END Purge;

  PROCEDURE HashCurrentId(VAR bucket : HashBucketType);
  BEGIN
    bucket := hashTotal MOD entryMax;
  END HashCurrentId;

  PROCEDURE StringSummary(); (* report usage. *)
  BEGIN
    WriteString("## String usage is ");
    WriteCard(tide,0);
    WriteString(" bytes of ");
    WriteCard(stringTableMax,0);
    WriteLn;
  END StringSummary;

(****************************************************************)

BEGIN (* initialization *)
  tide := 1;    tStart := 1;
  interim := 1; limit  := 0;
  empty := interim;
END Strings;

(****************************************************************)
(****************************************************************)
(* This module implements a closed hash table and a hash func-  *)
(* tion based on (currently 16-bit) rotates and adds. Probing   *)
(* uses a quadratic overflow function, which requires no multi- *)
(* plication. The number of hash buckets MUST be prime.         *)
(****************************************************************)

MODULE HashTable;

  IMPORT HashBucketType, Spellix, HashCurrentId,
         entryMax, InterimSpellix, StringsEqual, empty,
         Purge, TermSymbols, WordEnter, AbortMessage,
         Commit, ResSymbol, ResWordEnter, SetLimit;


  IMPORT Write, WriteLn, WriteString, WriteCard; 
         (* only needed for summary *)

  EXPORT SpellingIndex, LookupAndEnter, EnterString, HashSummary;

  VAR   hTable : ARRAY [0 .. entryMax - 1] OF Spellix;
        entryNum : CARDINAL;                (* number of entries *)

        collisions : ARRAY [0 .. 7] OF CARDINAL;
                (* number of collisions *)

  PROCEDURE HashSummary(); (* report usage etc. *)
    VAR ix : CARDINAL;
  BEGIN
    WriteString("## Hash table entries = ");
    WriteCard(entryNum,0);
    WriteString(" of ");
    WriteCard(entryMax,0);
    WriteLn;
 (*
    WriteString("Collisions  Occurrences");
    WriteLn;
    FOR ix := 0 TO 7 DO
      WriteCard(ix,0); Write(' ');
      WriteCard(collisions[ix],0);
      WriteLn;
    END;
  *)
  END HashSummary;

  PROCEDURE SpellingIndex(hash : HashBucketType) : Spellix;
  (* precondition  : hash corresponds to a loaded identifier;
     postcondition : result is spelling index of ident.       *)
  BEGIN
    RETURN hTable[hash];
  END SpellingIndex;

  PROCEDURE LookupAndEnter(VAR symbol : TermSymbols;
                           VAR hashIx : HashBucketType);
  (* precondition  : the value returned by InterimSpellix corresponds
                     to a validly marked spelling index. The string to
                     be entered is held in the string table starting
                     at location spix, and the contents of this string
                     have been hashed by calls to CopyAndHash
     postcondition : symbol is token of string (either res.
                     word or ident). If an ident then hashIx
                     is the index of entry. Otherwise hashIx is
                     unmodified.  If not a new ident then Purge
                     discards the string.        *)
    VAR inc : CARDINAL;
        spix   : Spellix; (* interim spellix value  *)
        testSp : Spellix; (* of bucket to be probed *)
        testIx : HashBucketType;
        looking : BOOLEAN;
  BEGIN
    inc := 1;
    spix := InterimSpellix();
    HashCurrentId(testIx);
    testSp := hTable[testIx];
    looking := (testSp <> empty) AND NOT StringsEqual(spix,testSp);  
    WHILE looking DO (* try another position *)
      testIx := (testIx + inc);
      IF testIx >= entryMax THEN (* wrap around *)
        testIx := testIx - entryMax;
        (* Since inc < entryMax, this is safe! *)
      END;
      INC(inc,2); (* prepare next probe *)
      IF inc >= entryMax THEN
        AbortMessage("Error: hash table near full.","");
      END;
      testSp := hTable[testIx];
      looking := (testSp <> empty) AND NOT StringsEqual(spix,testSp);    
    END;
    (* assert : no longer looking. But for which reason ? *)
    IF testSp = empty THEN (* insert entry *)
      hTable[testIx] := spix;
      INC(entryNum);
      Commit(); (* move up temp ptr. *)
      symbol := ident;
      hashIx := testIx;
(*
 *  code for accumulating hash table stats ...
 *      (* at exit, number of collisions is (inc - 1) / 2 *)
 *      inc := inc DIV 2;
 *      IF inc > 7 THEN inc := 7 END;
 *      INC(collisions[inc]);
 *)
    ELSE (* could be reserved word *)
      symbol := ResSymbol(testSp); Purge(); (* and purge anyhow *)
      IF symbol = ident THEN hashIx := testIx END;
    END;
  END LookupAndEnter;

        (**************************************************)

PROCEDURE InsertResWord(str : ARRAY OF CHAR;
                        sym : TermSymbols);
  VAR dummyBucket : HashBucketType;
BEGIN
  ResWordEnter(str,sym);
  LookupAndEnter(sym,dummyBucket);
END InsertResWord;

PROCEDURE ResWordInit;
BEGIN
  InsertResWord("AND",   andSy);   InsertResWord("DIV",    divSy);
  InsertResWord("MOD",   modSy);   InsertResWord("NOT",    notSy);
  InsertResWord("REM",   remSy);   InsertResWord("NIL",    nilSy);
  InsertResWord("IN",    inSy);    InsertResWord("VAR",    varSy);
  InsertResWord("ARRAY", arraySy); InsertResWord("RECORD", recordSy);
  InsertResWord("SET",   setSy);   InsertResWord("OR",     orSy);
  InsertResWord("TO",    toSy);    InsertResWord("IMPORT", importSy);
  InsertResWord("OF",    ofSy);    InsertResWord("FROM",   fromSy);
  InsertResWord("BEGIN", beginSy); InsertResWord("CASE",   caseSy);
  InsertResWord("BY",    bySy);    InsertResWord("IF",     ifSy);
  InsertResWord("THEN",  thenSy);  InsertResWord("ELSIF",  elsifSy);
  InsertResWord("ELSE",  elseSy);  InsertResWord("LOOP",   loopSy);
  InsertResWord("EXIT",  exitSy);  InsertResWord("REPEAT", repeatSy);
  InsertResWord("UNTIL", untilSy); InsertResWord("WHILE",  whileSy);
  InsertResWord("DO",    doSy);    InsertResWord("WITH",   withSy);
  InsertResWord("FOR",   forSy);   InsertResWord("RETURN", returnSy);
  InsertResWord("END",   endSy);   InsertResWord("CONST",  constSy);
  InsertResWord("TYPE",  typeSy);  InsertResWord("MODULE", moduleSy);
  InsertResWord("QUALIFIED",qualifiedSy);
  InsertResWord("EXPORT",exportSy);
  InsertResWord("FORWARD",forwardSy);
  InsertResWord("POINTER",pointerSy);
  InsertResWord("DEFINITION",definitionSy);
  InsertResWord("IMPLEMENTATION",implementationSy);
  InsertResWord("PROCEDURE",procedureSy);
  SetLimit;
END ResWordInit;

PROCEDURE EnterString(str : ARRAY OF CHAR;
                  VAR hIx : HashBucketType);
  VAR sym : TermSymbols;
BEGIN
  WordEnter(str);
  LookupAndEnter(sym,hIx);
END EnterString;

        (**************************************************)


  VAR ix : CARDINAL;

BEGIN (* initialization *)
  FOR ix := 0 TO entryMax - 1 DO
    hTable[ix] := empty;
  END;
  entryNum := 0;
  FOR ix := 0 TO 7 DO
    collisions[ix] := 0;
  END;
  ResWordInit;
END HashTable;

(* ================================================================= *)

BEGIN
  (* assert : reserve words have already been inserted *)
  EnterString('$std$',stdBkt);
  EnterString('$anon$',anonBkt);
  EnterString("ALLOCATE",allocBkt);
  EnterString("DEALLOCATE",deallBkt);
  EnterString("SYSTEM",sysBkt);
  EnterString("LIBRARY",libBkt);
  EnterString("NONREC",nonRecBkt);
  EnterString("FOREIGN",foreignBkt);
  EnterString("INTERFACE",directBkt);
  EnterString("INLINE",inlineBkt);
END MkNameHandler.

