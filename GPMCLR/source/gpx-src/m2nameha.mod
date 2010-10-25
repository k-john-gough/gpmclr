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
(*			:  4-Dec-90 larger hash and string tabs *)
(*			: 28-Jul-91 fix of proc ResWordEnter	*)
(*			: 02-Apr-92 jrh add IncSourceRep	*)
(*			: 14-May-92 jrh RelaxLimit, GetFileName	*)
(*								*)
(*   =============== merged mips and i386 source ============	*)
(*			   kjg 22 Mar 93			*)
(*                                                              *)
(****************************************************************
$Log: m2nameha.mod,v $
Revision 1.8  1997/01/16 04:02:36  gough
new procedure ExcludeExt (exclude extensions).
New keyword PRE, removal fo SetLimit3.

Revision 1.7  1996/11/27 02:02:51  lederman
add FINALLY, EXCEPT and RETRY

Revision 1.6  1996/10/09 05:53:37  lederman
make string & hash tables dynamic - get sizes from M2STRING & M2HASH

Revision 1.5  1996/08/06 23:47:01  gough
insert reserved word STRING

Revision 1.4  1996/07/05 04:25:47  gough
entering PACKEDSET as synonym for SET

Revision 1.3  1996/01/08 05:28:41  gough
remove use of uninitialised variable limit2

Revision 1.2  1994/07/01 04:54:04  lederman
bitsInWord refers to 'host' word here

# Revision 1.1  1994/04/07  05:02:11  lederman
# Initial revision
*****************************************************************)

IMPLEMENTATION MODULE M2NameHandler;

(*      +---------------------------------------+
        |  MODULE M2NameHandler                 |
        |   +-------------------------------+   |
        |   |  MODULE Strings               |   |
        |   +-------------------------------+   |
        |   +-------------------------------+   |
        |   |  MODULE HashTable             |   |
        |   +-------------------------------+   |
        +---------------------------------------+              *)

IMPORT SYSTEM;
FROM Storage IMPORT ALLOCATE, DEALLOCATE;
FROM M2Alphabets IMPORT Spellix, HashBucketType, TerminalSymbols;
FROM M2InOut IMPORT WriteSb, WriteObjByte, AbortMessage, Error;
FROM Ascii IMPORT nul;
FROM StdError IMPORT Write, WriteString, WriteLn, WriteCard; (* interim *)
FROM ProgArgs IMPORT Assert, EnvironString;
FROM WholeStr IMPORT ConvResults, StrToCard;
FROM RealMath IMPORT sqrt;
FROM Types    IMPORT Card16;

(* $I- *)

  VAR base, hLim : POINTER TO CARDINAL;

  PROCEDURE Summary();
  BEGIN
    StringSummary();
    HashSummary();
    ALLOCATE(hLim,40000);
    WriteString("Heap usage = ");
    WriteCard(SYSTEM.CAST(CARDINAL,hLim) - SYSTEM.CAST(CARDINAL,base),0);
    WriteLn;
  END Summary;

(****************************************************************)

MODULE Strings;

  FROM SYSTEM IMPORT CAST;

  IMPORT Spellix, entryMax, TerminalSymbols, SpellingIndex,
	 HashBucketType, Error, AbortMessage, Assert,
	 EnvironString, ConvResults, StrToCard, ALLOCATE;

  IMPORT Write, WriteString, WriteCard, WriteLn, (* only needed for summary *)
         nul, WriteObjByte, WriteSb;

  EXPORT GetSourceRep, GetFileName, 
	 StringsEqual, StringSummary, StringTable,
         MarkInterimSpellix, InterimSpellix, Purge, empty,
         MarkEnd, WordEnter, ResWordEnter, ResSymbol, CopyString,
         SetLimit, SetLowLimit, ExcludeExt,
         CopyChar, CopyAndHash, HashCurrentId,
         (* set operations *)
         MakeEmptySet, SetInclude, SetExclude, SetRngIncl,
         SetRelop, SetInOp, SetOperate, Commit, GetString, DumpBytes;

  CONST ovrflo = "String table overflow. Set M2STRING to increase size.";

  VAR   stringTableMax : Spellix;  (* size of string table *)

  VAR   table : POINTER TO ARRAY[1 .. 1] OF CHAR;
        (* A Spellix is actually an index into this array *)

  VAR   interim  : Spellix;
        empty    : Spellix;  (* an illegal entry *)
        tide     : Spellix;
        tStart   : Spellix;  (* start of temporaries *)
        limit    : Spellix;  (* this is the highTide mark after
                                all reserved word insertions *)
	loLim    : Spellix;  (* limit without, PRE, STRING *)

  VAR   hashTotal : CARDINAL;

  (**************************************************)
  (* some reserved word handling utility procedures *)
  (**************************************************)

  PROCEDURE ResWordEnter(str : ARRAY OF CHAR;
                         sym : TerminalSymbols);
    VAR ix : CARDINAL; (* index into string  *)
  BEGIN
    table^[tide] := CHR(ORD(sym));
    INC(tide);
    MarkInterimSpellix;
    FOR ix := 0 TO HIGH(str) DO
   (* 
    *   Beware that HIGH is now (since may 91) 
    *	equal to the string length, so that
    *   the string included the nul byte
    *   this code is safe with either 
    *   version of M2Traversal (kjg 28-Jul-91)
    *)
      IF str[ix] <> nul THEN
        CopyAndHash(str[ix]);
      END;
    END;
    MarkEnd();
  END ResWordEnter;

  PROCEDURE ResSymbol(sp : Spellix) : TerminalSymbols;
  BEGIN
    IF sp < limit THEN
      RETURN VAL(TerminalSymbols,ORD(table^[sp - 1]));
    ELSE RETURN ident
    END;
  END ResSymbol;

  PROCEDURE SetLimit;
  BEGIN
    limit := tide;
  END SetLimit;

  PROCEDURE SetLowLimit;
  BEGIN
    loLim := tide;
  END SetLowLimit;

  PROCEDURE ExcludeExt;
  BEGIN
    limit := loLim;
  END ExcludeExt;

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

  PROCEDURE CopyString(str : ARRAY OF CHAR;
		  VAR  spx : Spellix);
    VAR ix : CARDINAL; ch : CHAR;
  BEGIN
    ix := 0; spx := tide; ch := str[0];
    WHILE ch <> nul DO
      table^[tide] := ch;
      INC(ix); INC(tide);
      IF ix <= HIGH(str) THEN ch := str[ix] ELSE ch := nul END;
    END;
    table^[tide] := nul; INC(tide);
  END CopyString;

  PROCEDURE Commit();
  BEGIN
    tStart := tide;
  END Commit;

  PROCEDURE GetString(spix : Spellix; VAR str : ARRAY OF CHAR);
    VAR ch : CHAR; ix : CARDINAL;
  BEGIN
    FOR ix := 0 TO HIGH(str) - 2 DO
      ch := table^[spix];
      str[ix] := ch;
      IF ch = "" THEN RETURN END;
      INC(spix);
    END;
    str[HIGH(str) - 1] := "";
  END GetString;

  PROCEDURE DumpBytes(spix : Spellix; num : CARDINAL);
    VAR ch : CHAR; ix : CARDINAL;
  BEGIN
    IF num = 0 THEN
      REPEAT
        ch := table^[spix]; WriteSb(ch); INC(spix);
      UNTIL ch = nul;
    ELSE
      FOR ix := 1 TO num DO
        WriteSb(table^[spix]); INC(spix);
      END;
    END;
  END DumpBytes;

  PROCEDURE StringTable(spix : Spellix) : CHAR;
  BEGIN
    RETURN table^[spix]
  END StringTable;

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
    IF spix < limit THEN
      str[idx] := "_"; INC(idx);
    END;
    WHILE (idx < HIGH(str)) AND (table^[spix] <> nul) DO
      str[idx] := table^[spix];
      INC(idx); INC(spix);
    END;
    str[idx] := nul;
  END GetSourceRep;

  PROCEDURE GetFileName(ident : HashBucketType;
                         VAR str : ARRAY OF CHAR;
                         VAR idx : CARDINAL);
  (* As for GetSourceRep, but NEVER prefix with "_".
     Use for file names which can't clash with C.    *)

    VAR spix : Spellix;
  BEGIN
    IF ident >= entryMax THEN spix := empty;
    ELSE spix := SpellingIndex(ident);
    END;
    WHILE (idx < HIGH(str)) AND (table^[spix] <> nul) DO
      str[idx] := table^[spix];
      INC(idx); INC(spix);
    END;
    str[idx] := nul;
  END GetFileName;

  PROCEDURE StringsEqual(s1, s2 : Spellix) : BOOLEAN;
  BEGIN
    WHILE (table^[s1] = table^[s2]) AND (table^[s1] <> nul) DO
      INC(s1); INC(s2);
    END;
    RETURN table^[s1] = table^[s2]
  END StringsEqual;

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

  PROCEDURE CopyChar(ch : CHAR);
  (* postcondition : ch is added to end of current interim string *)
  BEGIN
    table^[tide] := ch;
    INC(tide);
  END CopyChar;

(* $T- *)
  PROCEDURE CopyAndHash(ch : CHAR);
  (* postcondition : ch is added to end of current interim string *)
    VAR msb : BOOLEAN;
  BEGIN
    table^[tide] := ch;
    INC(tide);
    (* rotate hashTotal *)
    msb := CAST(INTEGER,hashTotal) < 0;
    hashTotal := hashTotal * 2 + ORD(ch) + ORD(msb);
  END CopyAndHash;
(* $T= *)

  PROCEDURE MarkEnd();
  (* postcondition : String is terminated by the
                     reserved value SYSTEM.TermChar		*)
  BEGIN
    table^[tide] := nul;
    IF tide >= stringTableMax THEN
      AbortMessage(ovrflo);
    END;
    INC(tide);
  END MarkEnd;

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
    WriteLn;
    WriteString("String usage is ");
    WriteCard(tide,0);
    WriteString(" bytes of ");
    WriteCard(stringTableMax,0);
    WriteLn;
  END StringSummary;

(****************************************************************)

  TYPE ByteSet = RECORD CASE (**) : BOOLEAN OF
                    TRUE : ord : CARDINAL;
                 | FALSE : set : BITSET;
                 END END;

  PROCEDURE MakeEmptySet(size : CARDINAL;
                       VAR ix : Spellix);
    VAR count : Spellix;
  BEGIN
    ix := tide; INC(tide,size);
    IF tide >= stringTableMax THEN
      AbortMessage(ovrflo);
    END; (* character zero is the empty set of 0..7 *)
    FOR count := ix TO tide DO table^[count] := nul END;
  END MakeEmptySet;

  PROCEDURE GetTempSet(size : CARDINAL) : Spellix;
    VAR ix : Spellix;
  BEGIN
    ix := tide; INC(tide,size);
    IF tide >= stringTableMax THEN
      AbortMessage(ovrflo);
    END;
    RETURN ix;
  END GetTempSet;

  PROCEDURE SetInclude(ix : Spellix; el : CARDINAL);
    VAR temp : ByteSet;
  BEGIN
    ix := ix + el DIV 8;
    temp.ord := ORD(table^[ix]);
    INCL(temp.set,el MOD 8);
    table^[ix] := CHR(temp.ord);
  END SetInclude;

  PROCEDURE SetExclude(ix : Spellix; el : CARDINAL);
    VAR temp : ByteSet;
  BEGIN
    ix := ix + el DIV 8;
    temp.ord := ORD(table^[ix]);
    EXCL(temp.set,el MOD 8);
    table^[ix] := CHR(temp.ord);
  END SetExclude;

  PROCEDURE SetRngIncl(ix : Spellix; lo, hi : CARDINAL);
    VAR count : CARDINAL;
  BEGIN (* cheap and nasty version *)
    FOR count := lo TO hi DO SetInclude(ix,count) END;
  END SetRngIncl;

  PROCEDURE SetRelop(size : CARDINAL;
                     opr  : TerminalSymbols;
                     left, right : Spellix) : BOOLEAN;
    VAR ended : BOOLEAN; ix : CARDINAL;
        lch, rch : ByteSet;
  BEGIN
    CASE opr OF
      equals : ended := FALSE; ix := 0;
        WHILE NOT ended AND (ix < size) DO
          ended := table^[left] <> table^[right];
          INC(left); INC(right); INC(ix);
        END;
        tide := tStart;
        RETURN NOT ended;
    | notEq : ended := FALSE; ix := 0;
        WHILE NOT ended AND (ix < size) DO
          ended := table^[left] <> table^[right];
          INC(left); INC(right); INC(ix);
        END;
        tide := tStart;
        RETURN ended;
    | grEqual : ended := FALSE; ix := 0;
        WHILE NOT ended AND (ix < size) DO
          lch.ord := ORD(table^[left]);
          rch.ord := ORD(table^[right]);
          ended := NOT(lch.set >= rch.set);
          INC(left); INC(right); INC(ix);
        END;
        tide := tStart;
        RETURN NOT ended;
    | lessEq : ended := FALSE; ix := 0;
        WHILE NOT ended AND (ix < size) DO
          lch.ord := ORD(table^[left]);
          rch.ord := ORD(table^[right]);
          ended := NOT(lch.set <= rch.set);
          INC(left); INC(right); INC(ix);
        END;
        tide := tStart;
        RETURN NOT ended;
    END;
  END SetRelop;

  PROCEDURE SetInOp(left : CARDINAL; right : Spellix) : BOOLEAN;
    VAR temp : ByteSet;
  BEGIN
    temp.ord := ORD(table^[right + left DIV 8]);
    tide := tStart;
    RETURN left MOD 8 IN temp.set;
  END SetInOp;

  PROCEDURE SetOperate(size  : CARDINAL;
                       opr   : TerminalSymbols;
                   VAR left  : Spellix;
                       right : Spellix);
    VAR res : Spellix; (* pointer INTO the result set   *)
        tmp : Spellix; (* pointer INTO the orig left op *)
        ix  : CARDINAL;
  BEGIN (* tStart is top of permanent string space *)
    tmp := left;
    IF left >= tStart THEN (* left is temporary *)
      res := left; (* result stays in left set *)
    ELSIF right >= tStart THEN (* right is temporary *)
      res := right; left := res; (* result in right *)
    ELSE (* neither is temporary *)
      res := GetTempSet(size); left := res;
    END;
    CASE opr OF
      plus :
        FOR ix := 0 TO size - 1 DO
          table^[res] := CHR(CAST(CARDINAL,
              CAST(BITSET,ORD(table^[tmp])) + 
              CAST(BITSET,ORD(table^[right]))));
          INC(res); INC(tmp); INC(right);
        END;
    | minus :
        FOR ix := 0 TO size - 1 DO
          table^[res] := CHR(CAST(CARDINAL,
              CAST(BITSET,ORD(table^[tmp])) -
              CAST(BITSET,ORD(table^[right]))));
          INC(res); INC(tmp); INC(right);
        END;
    | star :
        FOR ix := 0 TO size - 1 DO
          table^[res] := CHR(CAST(CARDINAL,
              CAST(BITSET,ORD(table^[tmp])) * 
              CAST(BITSET,ORD(table^[right]))));
          INC(res); INC(tmp); INC(right);
        END;
    | slash :
        FOR ix := 0 TO size - 1 DO
          table^[res] := CHR(CAST(CARDINAL,
              CAST(BITSET,ORD(table^[tmp])) /
              CAST(BITSET,ORD(table^[right]))));
          INC(res); INC(tmp); INC(right);
        END;
    END;
    tide := res;
  END SetOperate;

(****************************************************************)

  PROCEDURE AllocateTable();
  VAR
    stringSizeStr : ARRAY [1 .. 80] OF CHAR;
    stringSize : CARDINAL;
    result : ConvResults;
  BEGIN
    (* String table size is given by environment variable, or default *)
    EnvironString ("M2STRING", stringSizeStr);
    IF stringSizeStr[1] = "" THEN
      stringSize := 63 * 1024;
    ELSE
      StrToCard(stringSizeStr,stringSize,result);
      Assert(result = strAllRight, "Bad M2STRING format");
      IF stringSize > 5120 * 1024 THEN
	stringSize := 5120 * 1024;	(* limit to 5 Meg *)
      END;
    END;
    ALLOCATE(table, stringSize);
    Assert(table # NIL, "Unable to allocate string table");
    stringTableMax := stringSize;
  END AllocateTable;

BEGIN (* initialization *)
  AllocateTable();
  tide := 1;    tStart := 1;
  interim := 1; limit  := 0;
  WordEnter("IllegalSpellix"); empty := interim;
END Strings;

(****************************************************************)
(****************************************************************)
(* This module implements a closed hash table and a hash func-  *)
(* tion based on (currently 16-bit) rotates and adds. Probing   *)
(* uses a quadratic overflow function, which requires no multi- *)
(* plication. The number of hash buckets MUST be prime.         *)
(****************************************************************)

MODULE HashTable;

  IMPORT HashBucketType, Spellix, HashCurrentId, InterimSpellix,
	 StringsEqual, empty, Purge, TerminalSymbols, WordEnter,
	 AbortMessage, Commit, ResSymbol, ResWordEnter, SetLimit, SetLowLimit,
	 EnvironString, ConvResults, StrToCard, Card16, sqrt, ALLOCATE, Assert;

  IMPORT Write, WriteLn, WriteString, WriteCard; 
         (* only needed for summary *)

  EXPORT entryMax, SpellingIndex, LookupAndEnter, EnterString, HashSummary;

  VAR entryMax : HashBucketType; (* size of Hash table *)
				 (* this MUST be a prime number *)

  VAR   hTable : POINTER TO ARRAY HashBucketType OF Spellix;
        entryNum : CARDINAL;                (* number of entries *)


  PROCEDURE HashSummary(); (* report usage etc. *)
    VAR ix : CARDINAL;
  BEGIN
    WriteString("Hash table entries = ");
    WriteCard(entryNum,0);
    WriteString(" of ");
    WriteCard(entryMax,0);
    WriteLn;
  END HashSummary;


  PROCEDURE SpellingIndex(hash : HashBucketType) : Spellix;
  (* precondition  : hash corresponds to a loaded identifier;
     postcondition : result is spelling index of ident.       *)
  BEGIN
    RETURN hTable^[hash];
  END SpellingIndex;

  PROCEDURE LookupAndEnter(VAR symbol : TerminalSymbols;
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
    testSp := hTable^[testIx];
    looking := (testSp <> empty) AND NOT StringsEqual(spix,testSp);  
    WHILE looking DO (* try another position *)
      testIx := (testIx + inc);
      IF testIx >= entryMax THEN (* wrap around *)
        testIx := testIx - entryMax;
        (* Since inc < entryMax, this is safe! *)
      END;
      INC(inc,2); (* prepare next probe *)
      IF inc >= entryMax THEN
        AbortMessage("Hash table nearly full. Set M2HASH to increase size.");
      END;
      testSp := hTable^[testIx];
      looking := (testSp <> empty) AND NOT StringsEqual(spix,testSp);    
    END;
    (* assert : no longer looking. But for which reason ? *)
    IF testSp = empty THEN (* insert entry *)
      hTable^[testIx] := spix;
      INC(entryNum);
      Commit(); (* move up temp ptr. *)
      symbol := ident;
      hashIx := testIx;
    ELSE (* could be reserved word *)
      symbol := ResSymbol(testSp); Purge(); (* and purge anyhow *)
      IF symbol = ident THEN hashIx := testIx END;
    END;
  END LookupAndEnter;

        (**************************************************)

PROCEDURE InsertResWord(str : ARRAY OF CHAR;
                        sym : TerminalSymbols);
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
  InsertResWord("PACKEDSET",setSy);
  InsertResWord("QUALIFIED",qualifiedSy);
  InsertResWord("EXPORT",exportSy);
  InsertResWord("FORWARD",forwardSy);
  InsertResWord("POINTER",pointerSy);
  InsertResWord("DEFINITION",definitionSy);
  InsertResWord("IMPLEMENTATION",implementationSy);
  InsertResWord("PROCEDURE",procedureSy);

  InsertResWord("FINALLY",finallySy);
  InsertResWord("EXCEPT",exceptSy);
  InsertResWord("RETRY",retrySy);
  SetLowLimit;
  InsertResWord("STRING",stringSy);
  InsertResWord("PRE",preconSy);
  SetLimit;
END ResWordInit;

PROCEDURE EnterString(str : ARRAY OF CHAR;
                  VAR hIx : HashBucketType);
  VAR sym : TerminalSymbols;
BEGIN
  WordEnter(str);
  LookupAndEnter(sym,hIx);
END EnterString;

        (**************************************************)

PROCEDURE AllocateTable();

  TYPE Primes = ARRAY [0 .. 606] OF HashBucketType;
  CONST prime = (* 500 .. MAX(HashBucketType) in steps of about 100 *)
Primes {503,  607,  709,  809,  911, 1013, 1117, 1217, 1319, 1423, 1523,
 1627, 1733, 1847, 1949, 2053, 2153, 2267, 2371, 2473, 2579, 2683, 2789,
 2897, 2999, 3109, 3209, 3313, 3413, 3517, 3617, 3719, 3821, 3923, 4027,
 4127, 4229, 4337, 4441, 4547, 4649, 4751, 4861, 4967, 5077, 5179, 5279,
 5381, 5483, 5591, 5693, 5801, 5903, 6007, 6113, 6217, 6317, 6421, 6521,
 6637, 6737, 6841, 6947, 7057, 7159, 7283, 7393, 7499, 7603, 7703, 7817,
 7919, 8039, 8147, 8263, 8363, 8467, 8573, 8677, 8779, 8887, 8999, 9103,
 9203, 9311, 9413, 9521, 9623, 9733, 9833, 9941,10061,10163,10267,10369,
10477,10589,10691,10799,10903,11003,11113,11213,11317,11423,11527,11633,
11743,11863,11969,12071,12197,12301,12401,12503,12611,12713,12821,12923,
13033,13147,13249,13367,13469,13577,13679,13781,13883,13997,14107,14207,
14321,14423,14533,14633,14737,14843,14947,15053,15161,15263,15373,15473,
15581,15683,15787,15887,15991,16091,16193,16301,16411,16519,16619,16729,
16829,16931,17033,17137,17239,17341,17443,17551,17657,17761,17863,17971,
18077,18181,18287,18397,18503,18617,18719,18839,18947,19051,19157,19259,
19373,19477,19577,19681,19793,19913,20021,20123,20231,20333,20441,20543,
20663,20771,20873,20981,21089,21191,21313,21419,21521,21647,21751,21851,
21961,22063,22171,22271,22381,22481,22613,22717,22817,22921,23021,23131,
23251,23357,23459,23561,23663,23767,23869,23971,24071,24179,24281,24391,
24499,24611,24733,24841,24943,25057,25163,25301,25409,25523,25633,25733,
25841,25943,26053,26153,26261,26371,26479,26591,26693,26801,26903,27011,
27127,27239,27361,27479,27581,27689,27791,27893,27997,28097,28201,28307,
28409,28513,28619,28723,28837,28949,29059,29167,29269,29383,29483,29587,
29717,29819,29921,30029,30133,30241,30341,30449,30553,30661,30763,30869,
30971,31079,31181,31307,31469,31573,31687,31793,31907,32009,32117,32233,
32341,32441,32561,32687,32789,32909,33013,33113,33223,33329,33457,33563,
33679,33791,33893,33997,34123,34231,34337,34439,34543,34649,34757,34871,
34981,35081,35201,35311,35419,35521,35671,35771,35879,35983,36083,36187,
36293,36433,36541,36643,36749,36857,36973,37087,37189,37307,37409,37511,
37619,37747,37847,37951,38053,38153,38261,38371,38501,38603,38707,38821,
38921,39023,39133,39233,39341,39443,39551,39659,39761,39863,39971,40087,
40189,40289,40423,40529,40637,40739,40841,40949,41051,41161,41263,41381,
41491,41593,41719,41843,41947,42061,42169,42281,42391,42491,42611,42719,
42821,42923,43037,43151,43261,43391,43499,43607,43711,43853,43961,44071,
44171,44273,44381,44483,44587,44687,44789,44893,45007,45119,45233,45337,
45439,45541,45641,45751,45853,45953,46061,46171,46271,46381,46489,46589,
46691,46807,46919,47041,47143,47251,47351,47459,47563,47681,47791,47903,
48017,48119,48221,48337,48437,48539,48647,48751,48857,48973,49081,49193,
49297,49409,49523,49627,49727,49831,49937,50047,50147,50261,50363,50497,
50599,50707,50821,50923,51031,51131,51239,51341,51449,51551,51659,51767,
51869,51971,52081,52181,52289,52391,52501,52609,52709,52813,52919,53047,
53147,53267,53377,53479,53591,53693,53813,53917,54037,54139,54251,54361,
54469,54577,54679,54779,54881,54983,55103,55207,55313,55439,55541,55661,
55763,55871,55987,56087,56197,56299,56401,56501,56611,56711,56813,56921,
57037,57139,57241,57347,57457,57557,57667,57773,57881,57991,58099,58199,
58309,58411,58511,58613,58727,58831,58937,59051,59159,59263,59369,59471,
59581,59693,59797,59921,60029,60133,60251,60353,60457,60589,60689,60793,
60899,61001,61121,61223,61331,61441,61543,61643,61751,61861,61961,62071,
62171,62273,62383,62483,62591,62701,62801,62903,63029,63131,63241,63347,
63463,63577,63689,63793,63901,64007,64109,64217,64319,64433,64553,64661,
64763,64871,64997,65099,65203,65309,65413,65521};

  VAR ix : CARDINAL;
      hashSizeStr : ARRAY [1..80] OF CHAR;
      hashSize : CARDINAL;
      result : ConvResults;
  BEGIN
    (* Hash table size is given by environment variable, or default *)
    EnvironString("M2HASH", hashSizeStr);
    IF hashSizeStr[1] = "" THEN
      hashSize := 5987;
    ELSE
      StrToCard(hashSizeStr,hashSize,result);
      Assert(result = strAllRight, "Bad M2HASH format");
    END;
    IF hashSize <= prime[0] THEN
      entryMax := prime[0];
    ELSE
      ix := 606;
      WHILE hashSize < prime[ix] DO DEC(ix) END;
      entryMax := prime[ix];
    END;
    ALLOCATE(hTable, entryMax*SIZE(Spellix));
    Assert(hTable # NIL, "Unable to allocate hash table");
    FOR ix := 0 TO entryMax - 1 DO
      hTable^[ix] := empty;
    END;
  END AllocateTable;

BEGIN (* initialization *)
  AllocateTable();
  entryNum := 0;
  ResWordInit;
END HashTable;

(* ================================================================= *)
CONST bitsInWord = SIZE(SYSTEM.WORD) * 8;
TYPE  UsedSetPtr = POINTER TO ARRAY [0 .. 0] OF BITSET;

PROCEDURE InitUsed(VAR p : UsedSetPtr);
VAR 
  usedMax, ix : CARDINAL;
BEGIN
  usedMax := entryMax DIV bitsInWord;
  ALLOCATE(p, (usedMax + 1) * SIZE(BITSET));
  FOR ix := 0 TO usedMax DO p^[ix] := BITSET{} END;
END InitUsed;

PROCEDURE MarkUsed(p : UsedSetPtr; h : HashBucketType);
BEGIN
  INCL(p^[h DIV bitsInWord], h MOD bitsInWord);
END MarkUsed;

PROCEDURE CheckUsed(p : UsedSetPtr; h : HashBucketType) : BOOLEAN;
BEGIN
  Assert(p <> NIL);
  RETURN  h MOD bitsInWord IN p^[h DIV bitsInWord];
END CheckUsed;

PROCEDURE DispUsed(VAR p : UsedSetPtr);
  VAR usedMax : CARDINAL;
BEGIN
  usedMax := entryMax DIV bitsInWord;
  DEALLOCATE(p, (usedMax + 1) * SIZE(BITSET));
END DispUsed;

(* ================================================================= *)

BEGIN
  (* assert : reserve words have already been inserted *)
  ALLOCATE(base,4);
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
END M2NameHandler.
