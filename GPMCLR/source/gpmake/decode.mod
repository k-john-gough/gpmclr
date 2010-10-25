(*
 * =========== macro processed output from MPP  ==========
 *
 * input file  : decode.mpp
 * time stamp  : 2004:01:14::06:44:08
 *
 * output file : decode.mod
 * created at  : 2004:01:16::14:18:38
 *
 * options ... :  /Ddotnet86
 *
 * =======================================================
 *)

(* -- RCS header --
	$Log:	decode.mpp,v $
Revision 1.3  94/01/14  10:49:05  mboss
Added Windows NT changes.

Revision 1.2  93/11/03  08:59:17  mboss
Added DEC Alpha changes

Revision 1.1  93/03/25  14:31:20  mboss
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
(*             Modula-2 Compiler Source Module                  *)
(*                                                              *)
(*          Symbol File Reconstructor and Decoder		*)
(*                                                              *)
(*     (c) copyright 1990 Faculty of Information Technology     *)
(*                                                              *)
(*      original module : kjg july 1990                         *)
(*      modifications   : kjg Mar-92 version using Mk* libs	*)
(*                      : kjg 03-Aug-92 uses new GpFiles procs  *)
(*                      : pms 13-Jan-94 Added Windows NT changes*)
(*                                                              *)
(****************************************************************)



MODULE Decode;

IMPORT SYSTEM, StdError, TermSymbolsIO;

FROM InOut IMPORT Write, WriteString, WriteLn, WriteCard;
FROM RealInOut IMPORT WriteReal;

FROM MkAlphabets IMPORT 
	SymbolSet, TermSymbols, Spellix, HashBucketType, 
	LexAttType, ConBlock;

FROM MkNameHandler IMPORT 
	GetSourceRep, StringTable, SpellingIndex, EnterString;

FROM MkScanner   IMPORT lexAtt, symSmbl, GetSymSmbl, InitSymScan;

FROM MkInOut     IMPORT CloseSymFile,
			OpenSymFile,
			AbortMessage,
			MiddleString,
 			FileNameString;

FROM ProgArgs IMPORT GetArg, ArgNumber, Assert, UNIXexit;

    (*****************************************************)

TYPE    TyNodeClass = (II, ZZ, UU, RR,
                   bools, sets, enums, chars, ints, cards,
                   floats, doubles, adrs, words, bytes, arrays,
                   pointers, records, unions, procTypes,
                   hiddens,    (* imported opaque *)
                   opaqueTemp, (* own opaque type *)
                   funcTypes, S1, SS, subranges);

     TYPE TyNamDesc = RECORD
			sy : TermSymbols;
			mNam, iNam : HashBucketType;
		      END;

     VAR thisName  : HashBucketType; (* = thisMod^.name  *)
	 verbose, super : BOOLEAN;
	 indent : CARDINAL;
         lastTyp : TyNamDesc;

     CONST maxVerNum = 4;
	   minVerNum = 2;
    (*****************************************************)

     MODULE AnonNames;
       IMPORT HashBucketType, EnterString;
       EXPORT NewAnon;

       VAR   str  : ARRAY [0 .. 7] OF CHAR;
       CONST init = "$anon000";

       PROCEDURE NewAnon() : HashBucketType;
         VAR new : HashBucketType;
       BEGIN
         INC(str[7]);
         IF str[7] > "9" THEN
	   str[7] := "0";
	   INC(str[6]);
	   IF str[6] > "9" THEN
	     str[6] := "0";
	     INC(str[5]);
	   END;
	 END;
	 EnterString(str,new);
	 RETURN new;
       END NewAnon;

     BEGIN
       str := init;
     END AnonNames;
    (*****************************************************)

       TYPE  HexCodes = ARRAY [0 .. 15] OF CHAR;
       CONST code = HexCodes{"0","1","2","3","4","5","6","7",
			     "8","9","a","b","c","d","e","f"};

       PROCEDURE WriteHex(num : CARDINAL);
	 VAR str : ARRAY [0 .. 8] OF CHAR;
	     ix  : CARDINAL;
       BEGIN
	 str[8] := "H";
         FOR ix := 7 TO 0 BY -1 DO
	   str[ix] := code[num MOD 16];
	   num := num DIV 16;
	 END;
	 WriteString(str);
       END WriteHex;

       PROCEDURE WriteSet(sp : Spellix);
	 VAR ix,bx : CARDINAL;
	     set   : BITSET;
	     chr   : CARDINAL;
       BEGIN
	 Write("{");
         IF verbose THEN
	   INC(indent,2);
	   sp := sp + 3;
	   WriteString("+++");
	   FOR ix := 0 TO 3 DO
	     IF super THEN
	       set := SYSTEM.CAST(BITSET,ORD(StringTable(sp)));
	       Write(" ");
	       FOR bx := 7 TO 0 BY -1 DO
		 IF bx IN set THEN Write("1") ELSE Write(".") END;
	       END;
	     ELSE
	       chr := ORD(StringTable(sp));
	       Write(" ");
	       Write(code[chr DIV 16]);
	       Write(code[chr MOD 16]);
	     END;
	     DEC(sp);
	   END; (* for *)
	   DEC(indent,2);
	 ELSE WriteString("set");
	 END;
	 Write("}");
       END WriteSet;

       PROCEDURE DoIndent();
         VAR ind : CARDINAL;
       BEGIN
	 FOR ind := 0 TO indent DO Write(" ") END;
       END DoIndent;

    (*****************************************************)

       PROCEDURE Check(expected : TermSymbols);
       BEGIN
         IF symSmbl <> expected THEN 
	   AbortMessage("Corrupt symbol file","");
         END;
       END Check;

       PROCEDURE WriteSpix(sp : Spellix);
	 VAR ch : CHAR;
       BEGIN
         ch := StringTable(sp);
         WHILE ch <> "" DO
           Write(ch); INC(sp);
	   ch := StringTable(sp);
	 END;
       END WriteSpix;

      PROCEDURE DiagName(hsh : HashBucketType);
        VAR str : ARRAY [0 .. 79] OF CHAR;
            idx : CARDINAL;
      BEGIN
        idx := 0;
        GetSourceRep(hsh,str,idx);
        WriteString(str);
      END DiagName;

      PROCEDURE QualName(ty : TyNamDesc);
      BEGIN
	WITH ty DO
	  CASE sy OF
	  | dot   : IF super THEN WriteString("$own.") END;
	  | slash : IF super THEN WriteString("$std.") END;
	  | ident : DiagName(mNam); Write(".");
	  END;
	  DiagName(iNam);
	END
      END QualName;

    (****************************************************)

    PROCEDURE HeaderCheck();
    BEGIN (* Header = VersionNumber DefModName. *)
      IF (lexAtt.fixValue >= minVerNum) AND
	 (lexAtt.fixValue <= maxVerNum) THEN
	WriteString("(* version number ");
	WriteCard(lexAtt.fixValue,0);
	WriteString(" >= ");
	WriteCard(minVerNum,0);
	WriteString(", <= ");
	WriteCard(maxVerNum,0);
	WriteString(" OK *)");
	WriteLn;
        GetSymSmbl; (* read past fixNum *)
      ELSE 
	WriteString("Bad version number ... got value ");
	WriteCard(lexAtt.fixValue,0);
	WriteString(" should have been ");
	WriteCard(maxVerNum,0);
	AbortMessage(' Sorry',"");
      END;
      WriteString("DEFINITION MODULE ");
      thisName := lexAtt.hashIx;
      DiagName(thisName); Write(";");
(**)  Check(ident); GetSymSmbl; (* read past ident *)
      WriteLn;
    END HeaderCheck;

    PROCEDURE Marker(VAR tp : TyNamDesc);
    BEGIN
      tp.sy := symSmbl;
      IF symSmbl = ident THEN
	tp.mNam := lexAtt.hashIx;
        GetSymSmbl; (* ident *)
      END;
      GetSymSmbl; (* dot or slash *)
    END Marker; (* post : symSmbl = ident *)

    PROCEDURE QualIdent(VAR tp : TyNamDesc);
    BEGIN (* QualIdent = Marker ident. *)
      Marker(tp);;
      tp.iNam := lexAtt.hashIx;
      QualName(tp);
      GetSymSmbl; (* ident *)
    END QualIdent;

    PROCEDURE FieldSeq();
    BEGIN
      WHILE (symSmbl = ident) OR (symSmbl = nilSy) DO
	WriteLn;
        IF symSmbl = ident THEN (* ordinary field *)
          DoIndent();
	  DiagName(lexAtt.hashIx);
	  WriteString(" : ");
          GetSymSmbl;
          Type(); Write(";");
        ELSE  (* create dummy IdDesc *)
          GetSymSmbl; (* get past nilSy *)
(**)      Check(caseSy); GetSymSmbl;
	  DoIndent();
	  WriteString("CASE (* some type *) OF");
          WHILE symSmbl = bar DO GetSymSmbl;
	    WriteLn; DoIndent;
	    WriteString("| (* variant tag selectors *) :");
	    INC(indent,2);
            FieldSeq();
	    DEC(indent,2);
          END; (* while *)
(**)      Check(endSy); GetSymSmbl;
	  WriteLn;
	  DoIndent();
	  WriteString("END (* union type *);");
(**)      Check(fixNum); (* and get type size *)
	  IF verbose THEN 
	    WriteLn;
	    DoIndent();
	    WriteString("(* union size = ");
	    WriteCard(lexAtt.fixValue,0);
	    WriteString(" bytes *)");
	  END;
          GetSymSmbl;
        END; (* if *)
      END; (* while *)
    END FieldSeq;

    PROCEDURE RecType(tp : TyNamDesc);
    (* RecordType  = recordSy { Fields } endSy.
       Fields      = ident Type | UnionType.
       UnionType   = caseSy {bar {Fields}} endSy.             *)
    BEGIN
      WriteString("RECORD (* ");
      QualName(tp); WriteString(" *)");
      GetSymSmbl;
      INC(indent,2);
      FieldSeq();
      WriteLn;
      DEC(indent,2);
(**)  Check(endSy); GetSymSmbl;
      DoIndent();
      WriteString("END (* ");
      QualName(tp); WriteString(" *)");
    END RecType;

    PROCEDURE ProcType();
    (* ProcType = procedureSy lPar {Formal} rPar [colon Type] *)
    BEGIN
      GetSymSmbl;
(**)  Check(lPar); GetSymSmbl;
      Write("(");
      INC(indent);
      IF symSmbl = rPar THEN WriteString("(* no params *)") END;
      WHILE symSmbl <> rPar DO (* seqOf FormalType *)
(**)    Check(charNum);
	CASE lexAtt.charValue OF
	| 4C : (* skip *)
	| 5C : WriteString("VAR ");
	| 6C : WriteString("ARRAY OF ");
	| 7C : WriteString("VAR ARRAY OF ");
	ELSE WriteCard(ORD(lexAtt.charValue),0);
	END;
        GetSymSmbl; 
	Type();
	IF symSmbl <> rPar THEN 
	  Write(";");
	  WriteLn;
	  DoIndent();
	END;
      END;
      Write(")");
      DEC(indent);
      GetSymSmbl;
      IF symSmbl = colon THEN GetSymSmbl;
	WriteString(" : ");
        Type();
      END;
      IF symSmbl = preconSy THEN
	GetSymSmbl;
	Write(";"); WriteLn; DoIndent;
	WriteString(" PRE ");
	INC(indent,4); GetExp(); DEC(indent,4);
      END;
    END ProcType;

    TYPE ExprNodeClass = 
        (* this sequence MUST align with TermSymbols *)
        ( errNode, andNode, divNode, starNode,
          slashNode, modulusNode, remNode, plusNode,
          minusNode, orNode, equalsNode, notEqNode,
          greaterNode, grEqualNode, lessNode, lessEqNode,
          inNode, notNode,
                                negateNode, literalNode,
          desigNode, constructorNode, adrDesigNode, funcDesigNode,
          repCountNode, selConstNode, setDesigNode, castNode,
          openMarshallNode, fixedMarshallNode, preconNode);

    PROCEDURE GetExp();

      PROCEDURE GetDesig;
      BEGIN
	IF symSmbl = fixNum THEN
	  Write("#"); 
	  WriteCard(lexAtt.fixValue,0);
	  GetSymSmbl;
	ELSE
	  Check(ident); DiagName(lexAtt.hashIx); GetSymSmbl;
	  IF symSmbl = dot THEN
	    Write("."); GetSymSmbl;
	    Check(ident); DiagName(lexAtt.hashIx); GetSymSmbl;
	  END;
	END;
	LOOP
	  IF symSmbl = endSy THEN GetSymSmbl; RETURN;
	  ELSIF symSmbl = ident THEN
	    DiagName(lexAtt.hashIx); GetSymSmbl;
	  ELSIF symSmbl = upArrow THEN
	    Write("^"); GetSymSmbl;
	  ELSE
	    Check(lBrac); GetSymSmbl;
	    Write("[");
	    GetExp;
	    Write("]");
	  END;
	END;
      END GetDesig;

      PROCEDURE GetFuncDesig;
      BEGIN
	GetDesig;
	Check(lPar); GetSymSmbl; Write("("); INC(indent,6);
	IF symSmbl <> rPar THEN WriteLn END;
	WHILE symSmbl <> rPar DO
	   DoIndent;
	   GetExp;
	   IF symSmbl <> rPar THEN
	     Write(","); WriteLn; DoIndent;
	   END;
	END;
	GetSymSmbl; Write(")"); DEC(indent,6);
      END GetFuncDesig;

      PROCEDURE GetConstructor;
      BEGIN
	Check(lCurly); GetSymSmbl; Write("{"); INC(indent);
	WHILE symSmbl <> rCurly DO
	   GetExp;
	   IF symSmbl = nilSy THEN 
	     GetSymSmbl;
	   ELSE
	     WriteString(" .. "); GetExp;
	   END;
	   IF symSmbl <> rCurly THEN
	     Write(","); WriteLn; DoIndent;
	   END;
	END;
	GetSymSmbl; Write("}"); DEC(indent);
      END GetConstructor;

      VAR class : ExprNodeClass;
	  oldSy : TermSymbols;
    BEGIN
      IF symSmbl = constSy THEN ConDef();
      ELSE
	oldSy := symSmbl;
	GetSymSmbl;
	IF oldSy <= VAL(TermSymbols,negateNode) THEN
	  IF oldSy = VAL(TermSymbols,negateNode) THEN
	    WriteString("neg");
	  ELSE
	    TermSymbolsIO.Write(oldSy); 
	  END;
	  Write("("); 
	  INC(indent,4); 
	  WriteLn; DoIndent; GetExp();
	  IF oldSy <= inSy THEN
	    Write(","); WriteLn; DoIndent; GetExp();
	  END;
	  Write(")");
	  DEC(indent,4);
	ELSE
	  class := VAL(ExprNodeClass,ORD(oldSy));
	  CASE class OF
	  | desigNode        : GetDesig; 
	  | funcDesigNode    : GetFuncDesig;
	  | setDesigNode,
	    constructorNode  : GetConstructor;
	  END;
	END;
	Write(":");
	Type;
      END;
    END GetExp;

    PROCEDURE Type();
    (* Type = equals                  -- the last type
            | QualIdent               -- some known type
            | (plus QualIdent | nilSy) ActualType Size. 
                                      -- some new type   *)
      VAR low, high, count : CARDINAL;
	  tpName : TyNamDesc;
    BEGIN
      INC(indent,2);
      IF symSmbl = equals THEN 
	IF super THEN Write("@") END;
	QualName(lastTyp); GetSymSmbl; tpName := lastTyp;
      ELSIF symSmbl IN SymbolSet{slash,ident,dot} THEN
        QualIdent(tpName); (* modId not nec = thisMod *)
      ELSE (* actual type *)
        IF symSmbl = nilSy THEN
	  tpName.sy := dot;
	  tpName.iNam := NewAnon();
          GetSymSmbl;
        ELSE (* maybe must insert now *)
(**)      Check(plus); GetSymSmbl;
          QualIdent(tpName);
        END; (* nilSy ==> anon type *)
        CASE symSmbl OF (* can this be avoided if already known? *)
        | lPar : GetSymSmbl; 
	    WriteString(" (* actually ---");
	    WriteLn;
	    DoIndent();
	    count := 0;
	    Write("(");
	    IF symSmbl = ident THEN
	      DiagName(lexAtt.hashIx); GetSymSmbl;
	    END;
	    INC(indent);
            WHILE symSmbl = ident DO
	      WriteString(",	(* "); 
	      WriteCard(count,0); INC(count);
	      WriteString(" *)"); 
	      WriteLn; 
	      DoIndent();
	      DiagName(lexAtt.hashIx); GetSymSmbl;
            END;
	    DEC(indent);
	    WriteString(");	(* "); 
	    WriteCard(count,0);
	    WriteString(" *)"); 
(**)        Check(rPar); GetSymSmbl;
	    WriteLn; DoIndent();
	    WriteString("--- end <"); QualName(tpName);
	    WriteString("> *)");
        | lBrac : GetSymSmbl;
(**)        Check(fixNum);
	    low := lexAtt.fixValue;
            GetSymSmbl;
(**)        Check(fixNum);
	    high := lexAtt.fixValue;
            GetSymSmbl;
	    WriteString(" (* ");
            Type();
	    GetSymSmbl;
	    Write("[");
	    WriteCard(low,0);
	    WriteString(" .. ");
	    WriteCard(high,0);
	    WriteString("] *)");
        | arraySy : GetSymSmbl;
	    WriteString(" (* actually ---");
	    WriteLn;
	    DoIndent();
	    WriteString("ARRAY ");
	    INC(indent,2);
            Type();
	    WriteString(" OF ");
(**)        Check(ofSy); GetSymSmbl;
	    INC(indent,2);
            Type();
	    DEC(indent,4);
	    WriteLn; DoIndent();
	    WriteString("--- end <"); QualName(tpName);
	    WriteString("> *)");
        | notEq : GetSymSmbl;
	    WriteString(" (* opaque *)");
        | setSy : GetSymSmbl;
	    WriteString(" (* SET OF ");
            Type();
	    WriteString(" *)");
        | pointerSy : GetSymSmbl;
	    WriteString(" (* actually ---");
	    WriteLn;
	    DoIndent();
	    WriteString("POINTER TO ");
            Type();
	    WriteLn; DoIndent();
	    WriteString("--- end <"); QualName(tpName);
	    WriteString("> *)");
        | recordSy : 
	    WriteString(" (* actually ---");
	    WriteLn;
	    DoIndent();
            RecType(tpName);
        | procedureSy : 
	    WriteLn;
	    DoIndent();
	    ProcType();
        | stringSy : GetSymSmbl;
	    WriteString(" (* actually ---");
	    WriteLn;
	    DoIndent();
	    WriteString("STRING OF ");
            Type();
	    WriteLn; DoIndent();
	    WriteString("--- end <"); QualName(tpName);
	    WriteString("> *)");
        ELSE AbortMessage('bad type begin symbol in SYM',"");
        END;
(**)    Check(fixNum); (* and get type size *)
	IF verbose THEN 
	  WriteLn;
	  DoIndent();
	  WriteString("(* tsize = ");
	  WriteCard(lexAtt.fixValue,0);
	  WriteString(" bytes *)");
	END;
	GetSymSmbl;
      END;
      DEC(indent,2);
      lastTyp := tpName;
    END Type;

    PROCEDURE ConDef();
    (* ConDef = constSy ident Value .
       Value  = fixNum CharNum [Type] | charNum | floatNum 
              | charLit | litstring | bigSetCon Type 
	      | heapConst Type | nilSy. *)
      VAR con : CARDINAL;
	  spix : Spellix;
	  heap : SYSTEM.ADDRESS;
	  class : TyNodeClass;
    BEGIN
      WriteString("CONST ");
      GetSymSmbl; (* discard constSy *)
      DiagName(lexAtt.hashIx);
      WriteString(" = ");
      GetSymSmbl; (* discard ident *)
        CASE symSmbl OF
        | fixNum : (* stow value *)
            con := lexAtt.fixValue; GetSymSmbl;
(**)        Check(charNum); (* value is tyClass of const *)
            class := VAL(TyNodeClass,ORD(lexAtt.charValue));
            GetSymSmbl;
            IF (class = enums) OR (class = subranges) THEN 
	      Type();
	      Write("(");
	      WriteCard(con,0);
	      Write(")");
	    ELSE
	      WriteCard(con,0);
            END;
        | floatNum :
	    WriteReal(lexAtt.floatValue,0);
            GetSymSmbl;
        | litstring :
	    Write('"');
	    WriteSpix(lexAtt.stringIx);
	    Write('"');
            GetSymSmbl;
	| charLit, charNum :
            con := ORD(lexAtt.charValue);
	    IF (con >= ORD(" ")) AND (con <  177B) THEN
	      Write('"');
	      WriteSpix(lexAtt.stringIx);
	      Write('"');
	    ELSE
	      Write(CHR(con DIV 64 + ORD("0")));
	      Write(CHR(con DIV 8 MOD 8 + ORD("0")));
	      Write(CHR(con MOD 8 + ORD("0")));
	      Write("C");
	    END;
            GetSymSmbl;
        | bigSetCon : (* stow value and set typeDesc ptr... *)
	    spix := lexAtt.patternIx;
            GetSymSmbl;
            Type();
	    WriteSet(spix);
	| heapConst :
	    WriteString("{constructor}");
	    GetSymSmbl; (* read past heapConst symbol *)
            Type();
        | nilSy :
	    WriteString("NIL");
            GetSymSmbl;
        ELSE AbortMessage('bad const declaration',"");
        END; (* case *)
    END ConDef;

    PROCEDURE TypeDef();
    (* TypeDef = typeSy ident Type. *)
    BEGIN
      WriteString("TYPE ");
      GetSymSmbl; (* discard constSy *)
      DiagName(lexAtt.hashIx);
      WriteString(" = ");
      GetSymSmbl; (* discard ident *)
      Type();
      Write(";");
      WriteLn;
    END TypeDef;

    PROCEDURE VarDef();
    (*  VarDef = varSy ident Type. *)
    BEGIN
      WriteString("VAR ");
      GetSymSmbl; (* discard *)
      DiagName(lexAtt.hashIx);
      WriteString("	: ");
      GetSymSmbl; (* discard ident *)
      Type();
      Write(";");
      WriteLn;
    END VarDef;

    PROCEDURE GetProcDef(tp : TyNamDesc);
    (*  ProcDef = procedureSy ident Type. *)
    BEGIN
      GetSymSmbl; (* procedureSy *)
(**)  Check(ident);
      tp.iNam := lexAtt.hashIx;
      QualName(tp);
      GetSymSmbl;
      Type();
    END GetProcDef;

    PROCEDURE ProcDef();
      VAR ty : TyNamDesc;
    BEGIN
      WriteString("PROCEDURE ");
      ty.sy := dot;
      GetProcDef(ty);
      Write(";");
      WriteLn;
    END ProcDef;

    TYPE ShortName = ARRAY [0 .. 7] OF CHAR;
    TYPE TableType = ARRAY [CHR(0) .. CHR(34)] OF ShortName;

    CONST table = TableType {
	"ABS", "CAP", "CHR", "FLOAT", "LFLOAT", "SLOAT", "HIGH",
	"MIN", "MAX", "ODD", "ORD", "SIZE", "TRUNC", "VAL",
	"NEW", "DISPOSE", "LENGTH", "DEC", "EXCL", "HALT",
	"ABORT", "INC", "INCL", "TSIZE", "ADR", "CAST",
	"INCADR", "DECADR", "DIFADR", "SHIFT", "ROTATE",
	"UNIXexit", "UNIXtime", "Assert", "CALL"};

    PROCEDURE ConProc();
    (* ConProc = upArrow ident ActualProc.              *)
    (* ActualProc = charNum charNum -- standard procs   *)
    (*            | Marker ProcDef [bar].               *)
    (* Marker  = slash | dot | ident dot.               *)
      VAR dummy : TyNamDesc;
    BEGIN
      WriteString("CONST proc");
      GetSymSmbl; (* upArrow *)
      DiagName(lexAtt.hashIx);
(**)  Check(ident);
      GetSymSmbl; (* ident *)
      IF symSmbl = charNum THEN (* stFunc or stProc *)
        GetSymSmbl; (* charNum *)
	WriteString(" = $std.");
	WriteString(table[lexAtt.charValue]);
        GetSymSmbl; (* charNum *)
      ELSE
	WriteString(" = ");
	INC(indent,8);
        Marker(dummy);
	GetProcDef(dummy);
        IF symSmbl = bar THEN
          GetSymSmbl; (* bar *)
        END;
	DEC(indent,8);
      END;
      Write(";");
      WriteLn;
    END ConProc;

    PROCEDURE Definitions();
    (* Definition = { (ConDef | TypeDef | ProcDef | VarDef) }. *)
    BEGIN
      LOOP
        WriteLn;
        WriteString("  ");
        CASE symSmbl OF
        | constSy : ConDef(); Write(";"); WriteLn;
        | typeSy  : TypeDef();
        | varSy   : VarDef();
        | procedureSy : ProcDef();
        | upArrow : ConProc();
        | endSy   : EXIT;
        ELSE AbortMessage('bad SYM definition',"")
        END;
      END;
    END Definitions;

    PROCEDURE ParseSymbolFile;
    (*   Unit = Header ModuleImports SymbolModule ImportObjects eofSy .
         ModuleImports = lBrac {ident ModuleKey} rBrac .
         SymbolModule  = moduleSy { Definition } endSy .        *)
      VAR 
          hsh : HashBucketType;

    BEGIN (* assert: either mod not known or not loaded *)
      indent := 8;
      InitSymScan; 
      HeaderCheck();
      IF (symSmbl = nilSy) THEN
	(*
	  this next marks the exportNodes of system modules
          so as to ensure that they are not named in ref files 
	*)
	WriteString("	(* is !SYSTEM! *)");
	(*
	  and externProcs of !LIBRARY (nonRec) modules so that 
          they are not presumed to engage in indirect recursion 
	*)
        GetSymSmbl;
      ELSIF symSmbl = bar THEN
	WriteString("	(* is !LIBRARY! *)");
        GetSymSmbl;
      ELSIF symSmbl = fromSy THEN (* !FOREIGN (macro) module *)
	WriteString("	(* is FOREIGN *)");
        GetSymSmbl;
	IF symSmbl = litstring THEN
	  WriteLn;
	  WriteString('  IMPORT IMPLEMENTATION FROM "');
	  WriteSpix(lexAtt.stringIx);
	  WriteString('";');
	  GetSymSmbl;
	END;
	(*
	 *  and now test if it is also !INTERFACE FOR_C!
	 *)
	IF symSmbl = forSy THEN
	  GetSymSmbl;
	  WriteString(" (* actually is INTERFACE *)");
	END;
      END;
      WriteLn;
      Check(lBrac); GetSymSmbl;
      IF symSmbl = ident THEN 
	WriteString("  IMPORT"); WriteLn;
        hsh := lexAtt.hashIx;
	DoIndent();
	DiagName(hsh);
        GetSymSmbl; (* read past ident *)
	IF verbose THEN
	  WriteString(" (* key = ");
	  WriteHex(lexAtt.fixValue);
	  WriteString(" *)");
        END;
(**)    Check(keySy); GetSymSmbl; (* past keySy *)
        WHILE symSmbl = ident DO
          hsh := lexAtt.hashIx;
	  WriteString(","); WriteLn;
	  DoIndent();
	  DiagName(hsh);
          GetSymSmbl; (* read past ident *)
	  IF verbose THEN
	    WriteString(" (* key = ");
	    WriteHex(lexAtt.fixValue);
	    WriteString(" *)");
          END;
(**)      Check(keySy); GetSymSmbl; (* past keySy *)
        END; (* while *)
	Write(";");
        WriteLn;
      END;
(**)  Check(rBrac);    GetSymSmbl;
(**)  Check(moduleSy); GetSymSmbl;
      Definitions();
(**)  Check(endSy);    GetSymSmbl;
      WriteLn;
      WHILE symSmbl < keySy DO GetSymSmbl END; (* also stops on eofSy *)
      IF verbose THEN
	WriteString("(* own key = ");
	WriteHex(lexAtt.fixValue);
	WriteString(" *)");
	WriteLn;
      END;
(**)  Check(keySy); GetSymSmbl;
(**)  Check(eofSy); CloseSymFile();
      WriteString("END ");
      DiagName(thisName);
      Write(".");
      WriteLn;
    END ParseSymbolFile;

    PROCEDURE ChopExtension(VAR str : ARRAY OF CHAR);
      VAR ix : CARDINAL;
    BEGIN
      (*
       *  if name has extension then remove it
       *)
      FOR ix := 0 TO LENGTH(str) - 1 DO
	IF str[ix] = "." THEN str[ix] := "" END;
      END;
    END ChopExtension;

  VAR str : FileNameString;
      out : MiddleString;
      hsh : HashBucketType;
      ok  : BOOLEAN;
      arg : CARDINAL;


  PROCEDURE Usage;
  BEGIN
    StdError.WriteString("#Decode: usage: decode [/vV] <name>");
    StdError.WriteLn;
    StdError.WriteString("	<name> may be: a mixed case module name");
    StdError.WriteLn;
    StdError.WriteString("		       lower case module name");
    StdError.WriteLn;
    StdError.WriteString("		       filename (with any extension)");
    StdError.WriteLn;
    StdError.WriteString("	v ... verbose detail");
    StdError.WriteLn;
    StdError.WriteString("	V ... super-verbose");
    StdError.WriteLn;
    StdError.WriteString("	Output is sent to standard output stream");
    StdError.WriteLn;
    UNIXexit(1);
  END Usage;

BEGIN
  arg := ArgNumber();
  IF arg < 1 THEN Usage END;
  GetArg(0,str);
  verbose := FALSE; super := FALSE;
  IF (str[0] = "/") OR (str[0] = "-") THEN
    IF str[1] = "V" THEN super := TRUE END;
    IF CAP(str[1]) = "V" THEN verbose := TRUE; 
    ELSE WriteString("decode: Bad option character"); WriteLn;
    END;
    IF arg < 1 THEN Usage END;
    GetArg(1,str);
  END;
  ChopExtension(str);
  EnterString(str,hsh);
  OpenSymFile(hsh,out,ok);
  IF NOT ok THEN 
    WriteString("symbol file for '");
    WriteString(str);
    WriteString("' not found");
    WriteLn;
    AbortMessage("","");
  ELSIF verbose THEN
    StdError.WriteString("Decode: symbol file for '");
    StdError.WriteString(str);
    StdError.WriteString("' found at ");
    StdError.WriteString(out);
    StdError.WriteLn;
  END;
  ParseSymbolFile();
END Decode.

