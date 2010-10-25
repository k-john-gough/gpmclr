(****************************************************************)
(*                                                              *)
(*                Modula-2 Compiler Source Module               *)
(*                                                              *)
(*                  the Input-Output procedures                 *)
(*                                                              *)
(*     (c) copyright 1988 Faculty of Information Technology     *)
(*                                                              *)
(*        original module : kjg july 1987                       *)
(*        modifications   :                                     *)
(*        last modified   : 24-Mar-88                           *)
(*        last modified   : 17-Aug   Sort proc. in error report *)
(*                        : 26-Jan-89  posi. of persistent test *)
(*                        : 25-Feb-89  listing code             *)
(*                        : 27-Feb-89  new option -f            *)
(*                        : 04-Mar-89  uses m2errlst.dat        *)
(*			  : 23-Apr-89  procs for macro headers. *)
(*			    Mods to Include so that large nums  *)
(*			    of warnings cannot mask all errors  *)
(*			  : 15-Aug-89  messages go to stderr,   *)
(*			    error message buffer now 10 kBytes  *)
(*			  : 13-Mar-90  overflow flag handling   *)
(*			  : 30-Mar-90  longer filenames now ok  *)
(*			  : 13-Apr-90  new proc DiagName	*)
(*			  : 10-Dec-90  suppress w's with gpm -d *)
(*			  : 13-Apr-91  extra error messages	*)
(*			  : 10-Feb-92  error message pointer pos*)
(*			  : 03-Mar-92  import Spellix		*)
(*			  : 14-May-92  use GetFileName		*)
(*			  : 14-May-92  ignore invalid more opts	*)
(*			  :  1-Aug-92  kjg, use GpFiles procs   *)
(*								*)
(*   =============== merged mips and i386 source ============	*)
(*			   kjg 22 Mar 93			*)
(*                                                              *)
(****************************************************************
$Log: m2inout.mod,v $
Revision 1.4  1997/01/16 03:51:50  gough
        symbol file opening and closing procedures have been revised,
        distinguishing between opening an old file and a new file.
        New command line arguments C0 to C9 and x-, x+ are parsed.
        Reading symbol files now uses flength.o to buffer whole file.

Revision 1.3  1996/02/06 23:38:45  lederman
Don't ExplainMore() on "m" if we've already explainAll'd

Revision 1.2  1994/07/01 04:35:59  lederman
clean up ABORT message

# Revision 1.1  1994/04/07  04:55:24  lederman
# Initial revision
#
*****************************************************************
Revision 1.9  94/03/23  11:39:30  gough
Correct code to rely on automatic shortening of m2errlst.dat2 in GpFiles
*****************************************************************)

IMPLEMENTATION MODULE M2InOut;

  IMPORT SYSTEM, ProgArgs, Storage, FLength;
  FROM M2Alphabets IMPORT
	HashBucketType, Spellix, TerminalSymbols, Flags,
	FlagSet, ModStateFlags, ModStateSet;
  FROM M2NameHandler IMPORT GetSourceRep, GetFileName, CopyString;
  FROM M2NodeDefs  IMPORT modState;
  FROM M2MachineConstants IMPORT 
	InitForCLR, defDensity, optDensity,
	bigEndian, bytesInWord, fileNameLength, oldFileNameLength;
  FROM M2Scanner   IMPORT 
	SetFlagOn, InitializeOptions, CurrentFlags, 
	StartSyncCount, IsSynchronized;
  FROM UxFiles IMPORT
	File, Open, Create, Close, Delete, OpenMode,
	ReadByte, ReadNBytes, Reset, WriteByte,
	EndFile, GetPos, SetPos;
  FROM Ascii IMPORT ht, lf, cr, nul;
  IMPORT InOut, StdError;
  FROM ProgArgs IMPORT 
	Assert, EnvironString, UNIXtime, VersionTime, ArgNumber, GetArg;
  FROM M2SSUtilities IMPORT DisplayLeftType, DisplayRightType;
	(* this import links the two SCCs of imports *)
  FROM GpFiles IMPORT GpFindLocal, GpFindOnPath, GpCreateFile;


  (* ===================================================== *)
  (* ===================================================== *)
    CONST greetStrD = "gpmd: generic m2 to dcode version of ";
    CONST greetStrX = "gpmx: m2 to CIL version of ";
  (* ===================================================== *)
  (* ===================================================== *)

    PROCEDURE DiagName(hsh : HashBucketType);
      VAR str : ARRAY [0 .. 79] OF CHAR;
	  idx : CARDINAL;
    BEGIN
      idx := 0;
      GetSourceRep(hsh,str,idx);
      StdError.WriteString(str);
    END DiagName;

  (* ===================================================== *)
  (*            Global types and variables                 *)
  (* ===================================================== *)

    CONST eol = lf;

    TYPE  PathNameString = ARRAY [0 .. 1023] OF CHAR;
	  CharSet = SET OF CHAR;

    CONST FileNameChars = 
	    CharSet{'a'..'z', 'A'..'Z', '0'..'9', '_', '.', '-', '<', '>', "&"};

(*  VAR   lastPos  : Position; (* position of last symbol *)    *)
    VAR   linePos  : CARDINAL;
	  lineNum  : CARDINAL;

    VAR inFile,		(* input file -- .mod or .def  *)
	auxFile,	(* outgoing syx or rfx file    *) 
	outFile, 	(* the object file for output  *)
	lstFile,        (* the optional listing file   *)
	errFile,	(* the error message file      *)
	tmpFile : File; (* this holds the outfile name *)

	   iCount, iNumLeft : CARDINAL;

	   tmpName  : FileNameString; (* arg[1] | arg[2] *)
	   cfgName  : FileNameString; (* config filename *)
	   symPath  : PathNameString;
	   clrPath  : PathNameString;
	   extend   : FileNameString;
	   osString : FileNameString;
	   interactive,
           isWinNT,
	   useFilNm : BOOLEAN;        (* initialized in OpenInput
	                                 modified by ParseOptions *) 

  (*=============================================*)

  MODULE ListingControl;

    IMPORT lstFile, WriteByte, GpCreateFile, 
	   Close, symPath, errFile, bigEndian,
	   DisplayLeftType, DisplayRightType,
	   modState, ModStateFlags, ModStateSet,
	   ReadNBytes, SYSTEM, ReadByte, SetPos,
	   FileNameString, GpFindOnPath, inpName, ReadCh,
	   nul, ht, eol, cr, lineNum, StdError;

    EXPORT SetTermOnly,  (* terminal only messages    *)
	   output,       (* generic message procvars  *)
	   savOut,	 (* output saved with -I flag *)
	   explain,      (* ==> write error message   *)
	   Explain,      (* procedure which does this *)
	   explainAll,   (* ==> write extra message   *)
	   ExplainMore,  (* procedure which does this *)
	   StillMore,    (* procedure which does this *)
	   Number,       (* generic write number proc *)
	   GetErrList,   (* load error message array  *)
	   WriteString,  (* write to term. or to both *)
	   StartListing, (* create and open list file *)
	   EndListing,   (* flush list file and close *)
	   InitSkip,     (* initialize the skip proc. *)
	   EmitBanner;   (* write out banner line     *)

    TYPE SkipP  = PROCEDURE(CARDINAL);
		  (* skipping with or without listings  *)
	 WriteP = PROCEDURE(CHAR);
		  (* writing a char to either or both   *)

    VAR  output, savOut :
		  RECORD
	            skipLines : SkipP;
	            writeChar : WriteP; 
		  END; 

	 inpCh   : CHAR;
	 explain : BOOLEAN; 
	 explainAll : BOOLEAN; 
 
    PROCEDURE SetBoth;
    BEGIN
      output.skipLines := ListLines;
      output.writeChar := WriteBoth;
    END SetBoth;

    PROCEDURE SetTermOnly;
    BEGIN
      output.skipLines := SkipLines;
      output.writeChar := StdError.Write;
    END SetTermOnly;

    PROCEDURE FileOnly(ch : CHAR);
    BEGIN
      WriteByte(lstFile,ch);
    END FileOnly;

    PROCEDURE WriteBoth(ch : CHAR);
    BEGIN
      StdError.Write(ch); WriteByte(lstFile,ch);
    END WriteBoth;

    PROCEDURE WriteNumber(num : CARDINAL; wrt : WriteP);
      VAR ix : CARDINAL; str : ARRAY [0 .. 4] OF CHAR;
    BEGIN
      str := "     "; ix := 4;
      WHILE num > 0 DO
	str[ix] := CHR(num MOD 10 + ORD("0"));
	num := num DIV 10; DEC(ix);
      END;
      FOR ix := 0 TO 4 DO wrt(str[ix]) END; 
    END WriteNumber;

    PROCEDURE Number(num : CARDINAL);
    BEGIN
      WriteNumber(num,output.writeChar);
    END Number;

    PROCEDURE Explain(errNo : CARDINAL);
      VAR ix : CARDINAL;
	  ch : CHAR;
    BEGIN
      SetPos(errFile,(errNo - 1) * 4);
      IF bigEndian THEN
	ReadByte(errFile,ch); ix := ORD(ch);
	ReadByte(errFile,ch); ix := ix * 100H + ORD(ch);
	ReadByte(errFile,ch); ix := ix * 100H + ORD(ch);
	ReadByte(errFile,ch); ix := ix * 100H + ORD(ch);
      ELSE
	ReadByte(errFile,ch); ix := ORD(ch);
	ReadByte(errFile,ch); INC(ix,ORD(ch) * 100H);
	ReadByte(errFile,ch); INC(ix,ORD(ch) * 10000H);
	ReadByte(errFile,ch); INC(ix,ORD(ch) * 1000000H);
      END;
 (* This test is a nuisance as the error file
  * grows so lets throw caution to the wind
  *   IF ix < 50000 THEN
  *)
	SetPos(errFile,ix);
	WriteString(" **** ");
	ReadByte(errFile,ch);
	WHILE (ch <> eol) AND (ch <> cr) DO
	  output.writeChar(ch); ReadByte(errFile,ch);
	END;
	WriteString(" ****");
	output.writeChar(eol);
  (*  END;
  *)
    END Explain;

  CONST str = 
"----------------------------------------------------------------------------";

    PROCEDURE ExplainMore();
      VAR ch : CHAR;
	  ln : CARDINAL;
    BEGIN
	ln := 0;
	WriteString("---- More info. ----"); 
	output.writeChar(eol);
	ReadByte(errFile,ch);
	WHILE (ch <> "") AND (ch <> "\") AND (ln < 24) DO
	  output.writeChar(ch); ReadByte(errFile,ch);
	  IF ch = cr THEN ReadByte(errFile,ch) END;
	  IF ch = eol THEN INC(ln) END;
	END;
	ReadByte(errFile,ch);
	WriteString(str);
	output.writeChar(eol);
    END ExplainMore;

    PROCEDURE StillMore();
      VAR ch : CHAR;
    BEGIN
      ReadByte(errFile,ch);
      IF ch < " " THEN ReadByte(errFile,ch) END; (* get past lf for DOS *)
      IF ch <> ">" THEN RETURN;
      ELSE
	ReadByte(errFile,ch);
	WHILE (ch <> "") AND (ch <> "\") DO
	  output.writeChar(ch); ReadByte(errFile,ch);
	  IF ch = "<" THEN 
	    DisplayLeftType(); ReadByte(errFile,ch);
	  ELSIF ch = ">" THEN 
	    DisplayRightType(); ReadByte(errFile,ch);
	  END;
	END;
	WriteString(str);
	output.writeChar(eol);
      END;
    END StillMore;

    PROCEDURE WriteString(str : ARRAY OF CHAR);
      VAR ix : CARDINAL;
    BEGIN
      ix := 0;
      WHILE (ix <= HIGH(str)) AND (str[ix] <> nul) DO
	output.writeChar(str[ix]); INC(ix);
      END
    END WriteString;

    PROCEDURE SkipLines(next : CARDINAL);
    BEGIN
      WHILE lineNum < next DO ReadCh(inpCh) END;
    END SkipLines;

    PROCEDURE ListLines(next : CARDINAL);
      VAR ok : BOOLEAN;
    BEGIN
      WHILE lineNum < next DO
	IF inpCh = nul THEN RETURN;
	ELSE
	  IF inpCh = eol THEN 
	    WriteNumber(lineNum,FileOnly);
	    WriteByte(lstFile,ht);
	  END;
	END;
	ReadCh(inpCh); WriteByte(lstFile,inpCh);
      END;
    END ListLines;

  (* --- error message file ------------------------------ *)

    PROCEDURE GetErrList();
      VAR read : CARDINAL; ok : BOOLEAN;
	  fName : FileNameString;
    BEGIN
      errFile := NIL;
      GpFindOnPath(symPath,"m2errlst","dat2",fName,errFile);
      explain := errFile <> NIL;
      IF NOT explain THEN 
	StdError.WriteString("**** can't open error list file ****");
	StdError.WriteLn;
      END;
    END GetErrList;

  (* --- listing file procedures -------------------------- *)

    PROCEDURE EmitBanner();
      CONST banner = 
	"============== <gardens point modula> compiler ==============";
    BEGIN
      WriteString(banner);
      output.writeChar(eol);
    END EmitBanner;

    PROCEDURE StartListing();
      VAR str : FileNameString;
	  idx : CARDINAL;
    BEGIN
      idx := 0;		(* truncate at first "." *)
      WHILE (inpName[idx] <> "") AND
	    (inpName[idx] <> ".") DO
	str[idx] := inpName[idx]; INC(idx);
      END;
      str[idx] := "";
      GpCreateFile(str,"lst",str,lstFile);
      IF lstFile <> NIL THEN SetBoth;
      ELSE
	StdError.WriteString("gpmd: can't open list file");
	StdError.WriteLn; SetTermOnly;
      END;
    END StartListing;

    PROCEDURE InitSkip();
    BEGIN
      output.writeChar(eol);
      inpCh := eol; (* force number on line 1 *)
    END InitSkip;

    PROCEDURE EndListing();
      VAR ok : BOOLEAN;
    BEGIN
     (*
      *  usually ListLines, but maybe Create failed, so
      *)
      output.skipLines(MAX(CARDINAL)); (* flush rest of lines *)
      Close(lstFile,ok);
    END EndListing;

  BEGIN
    explain := TRUE;
    explainAll := FALSE;
    SetTermOnly();
  END ListingControl;
  (*=============================================*)

(* --- main input file procedures ----------------------------- *)


  PROCEDURE ParseOptions(str : ARRAY OF CHAR);

    VAR ch : CHAR; ix : CARDINAL;
	initFlags : FlagSet;

    PROCEDURE BadOption(ch : CHAR);
    BEGIN
      StdError.WriteString("Bad option -");
      StdError.Write(ch); StdError.WriteLn;
    END BadOption;

  BEGIN (* assert: str is null terminated *)
    IF CAP(extend[0]) = "T" THEN INCL(modState,extensions) END;
    explain := TRUE;
    initFlags := FlagSet{indexTests, rangeTests, ovfloTests, stackTests};
    ch := str[1]; ix := 1;
    INCL(modState,cseElim);
    WHILE ch <> nul DO
      CASE ch OF
      (* ============================================= *)
      | "C" : INC(ix); ch := str[ix];
	      IF ("0" <= ch) AND (ch <= "8") THEN 
		optDensity := (ORD(ch) - ORD("0")) * 2;
		defDensity := optDensity;	(* override both! *)
	      ELSE (* ignore *)
	      END;
      | "I" : interactive := TRUE;
      | "N" : INC(ix); ch := str[ix];
	      IF ch = "c" THEN EXCL(modState,cseElim);
	      ELSE (* ignore *)
	      END;
      | "O" : INC(ix); ch := str[ix];
	      IF    ch = "c" THEN (* default *)
	      ELSIF ch = "f" THEN INCL(initFlags,fastCode);
	      ELSE BadOption(ch);
	      END;
      | "x" : INC(ix); ch := str[ix];
	      IF    ch = "+" THEN INCL(modState,extensions);
	      ELSIF ch = "-" THEN EXCL(modState,extensions);
	      ELSE BadOption(ch);
	      END;
      | "V" : INCL(modState,superVerbose);
	      INCL(modState,verbose);
	      explainAll := TRUE;
      | "X" : explainAll := TRUE;
      (* ============================================= *)
      | "a" : INCL(modState,assertOff);
      | "c" : INCL(modState,emitCil); InitForCLR();
      | "d" : INCL(modState,dangerous);
      | "f" : useFilNm := TRUE;
      | "g" : debugOn  := TRUE;
      | "i" : EXCL(initFlags,indexTests)
      | "l" : INCL(initFlags,listings);
      | "m" : INCL(modState,emitCil);
      | "n" : EXCL(modState,objectCode);
      | "p" : INCL(modState,profiling);
      | "r" : EXCL(initFlags,rangeTests);
      | "s" : EXCL(initFlags,stackTests);
      | "S" : INCL(modState,persistent);
      | "t" : EXCL(initFlags,ovfloTests);
      | "v" : INCL(modState,verbose);
      (* ============================================= *)
      ELSE BadOption(ch);
      END; (* case *)
      IF ch <> nul THEN INC(ix); ch := str[ix]; END;
    END;        
    InitializeOptions(initFlags);
  END ParseOptions;

  PROCEDURE OpenConfigFile;
    VAR ok : BOOLEAN;
  BEGIN
    GpFindOnPath(symPath,"gp2d","cfg",cfgName,inFile);
    Assert(inFile <> NIL,"File gp2d.cfg not found");
  END OpenConfigFile;

  PROCEDURE OpenInput;
  (* in case of errors, lexErrors is set in flags *)
    VAR str : FileNameString;
	ok  : BOOLEAN; 
	chIx : CARDINAL;
	argP : CARDINAL;
	argN : CARDINAL;
	timeStr : ARRAY[0 .. 29] OF CHAR;
  BEGIN
(*
    InOut.WriteString("GPMx args:");
    FOR argP := 0 TO ArgNumber() - 1 DO
      GetArg(argP, str);
      InOut.Write(" ");
      InOut.WriteString(str);
    END;
    InOut.WriteLn;
 *)
    IF CAP(osString[0]) = "W" THEN 
      isWinNT := TRUE; argP := 0;
    ELSE 
      isWinNT := FALSE; argP := 1;
    END;
    argN := ArgNumber();

    useFilNm := FALSE; interactive := FALSE;
    GetArg(argP,str); 
    IF str[0] = "-" THEN
      Assert(argN - argP = 3); INC(argP);
      ParseOptions(str);
    ELSE       
      Assert(argN - argP = 2);
      ParseOptions("-");	(* ensure initialization of flags Mar-93 *)
    END;
    GetArg(argP,tmpName); INC(argP);
    GetArg(argP,inpName);
    Open(inFile,inpName,ReadOnly,ok);
    IF NOT ok THEN  (* try some variations *)
      chIx := 0;
      WHILE (inpName[chIx] <> "") AND
	    (inpName[chIx] <> ".") DO INC(chIx) END;
      IF inpName[chIx] <> "." THEN 
	GpFindLocal(inpName,"mod",inpName,inFile);
	ok := inFile <> NIL;
      END;
    END;
    IF NOT ok THEN 
      GetArg(argP,inpName); (* fetch again *)
      WriteString("## file <<"); 
      WriteString(inpName);
      WriteString(">> ");
      AbortMessage(" can't open input file");
    ELSE
      IF listings IN CurrentFlags() THEN StartListing() END;
      IF (superVerbose IN modState) OR explainAll THEN
	IF listings IN CurrentFlags() THEN EmitBanner() END;
	VersionTime(timeStr);
        IF emitCil IN modState THEN
	  WriteString(greetStrX);
        ELSE
	  WriteString(greetStrD);
        END;
	WriteString(timeStr);
      END;
      IF verbose IN modState THEN
	IF listings IN CurrentFlags() THEN 
	  EmitBanner();
	  output.writeChar(eol);
	END;
	WriteString('Opening "');
	WriteString(inpName);
	WriteString('" as input'); output.writeChar(eol);
	WriteString("... Target configuration file ");
	WriteString(cfgName); output.writeChar(eol);
      END;
    END; 
    linePos := 0; lineNum := 1;
  END OpenInput;

  PROCEDURE ResetInput;
  BEGIN
    Reset(inFile);
    linePos := 0; lineNum := 1;
  END ResetInput;

  PROCEDURE ReadCh(VAR ch : CHAR);
  (* reads a character from the main input stream *)
  BEGIN
    ReadByte(inFile,ch);
    IF ch >= " " THEN
      INC(linePos);
      IF (ch = 377C) AND EndFile(inFile) THEN ch := nul END;
    ELSIF ch = eol THEN
      INC(lineNum); linePos := 0;
    ELSIF ch = ht THEN (* round to multiple of 8 *)
      INC(linePos,8); DEC(linePos,linePos MOD 8);
    END;
  END ReadCh;

  PROCEDURE MarkPosAndReadCh(VAR ch : CHAR);
  (* the current stream position is marked, and
     the next character in the stream is fetched  *)
  BEGIN
    lastPos.pos  := linePos;
    lastPos.line := lineNum;
    ReadByte(inFile,ch);
    IF ch >= " " THEN
      INC(linePos);
      IF (ch = 377C) AND EndFile(inFile) THEN ch := nul END;
    ELSIF ch = eol THEN
      INC(lineNum); linePos := 0;
    ELSIF ch = ht THEN (* round to multiple of 8 *)
      INC(linePos,8); DEC(linePos,linePos MOD 8);
    END;
  END MarkPosAndReadCh;

(* --- header lookup procedure -------------------------------- *)

  PROCEDURE FindHeaderPath( name : HashBucketType;
			VAR path : Spellix;
			VAR lNam : Spellix);
    VAR str : FileNameString; (* the full length name  *)
	new : FileNameString; (* the short length name *)
	out : PathNameString; (* the found path string *)
	ix : CARDINAL; 
	ok : BOOLEAN; ch : CHAR;
  BEGIN
    ix := 0; GetFileName(name,str,ix);
    IF verbose IN modState THEN WriteString("..... Header file ") END;
    GpFindOnPath(symPath,str,"h",out,tmpFile);
    IF verbose IN modState THEN
      WriteString(out); output.writeChar(eol);
    END;
    IF tmpFile <> NIL THEN 
      CopyString(out,path);
      Close(tmpFile,ok);
    ELSE
      ErrIdent(305,name); 
      SetFlagOn(filErrors);
    END;
  END FindHeaderPath;

(* --- symbol file reader procedures -------------------------- *)

  MODULE SymFileReader; (* ==================================== *)

  IMPORT 
	 Close, HashBucketType, FileNameString, 
	 PathNameString, GetFileName, File,
	 GpFindOnPath, emitCil, symPath, clrPath, eol,
	 FLength, SYSTEM, Storage, StdError,
	 modState, ModStateFlags,
	 WriteString, output, ReadNBytes, Assert;

  EXPORT OpenOldSymFile, ReadSb, CloseOldSymFile;

    TYPE   StackIx  = [0 .. 63];
	   BuffPtr  = POINTER TO ARRAY [0 .. 0] OF SYSTEM.BYTE;
	   BuffDesc = RECORD
			nextSb : CARDINAL;
			length : CARDINAL;
			buffer : BuffPtr;
		      END;

    VAR    bffStack : ARRAY StackIx OF BuffDesc;
	   bffTop   : StackIx;

    VAR    actual   : CARDINAL;

    PROCEDURE OpenOldSymFile(modHash : HashBucketType;
			     VAR  ok : BOOLEAN);
      VAR str : FileNameString; 
	  new : FileNameString; 
	  out : PathNameString;
	  ix  : CARDINAL;
	  oldFile : File;
    BEGIN
      INC(bffTop);
      ix := 0; GetFileName(modHash,str,ix);
      IF verbose IN modState THEN
	WriteString("... Importing <");
	WriteString(str);
	WriteString("> from ");
      END;

      oldFile := NIL;
      IF emitCil IN modState THEN 
                            GpFindOnPath(clrPath,str,"syx",out,oldFile) END;
      IF oldFile = NIL THEN GpFindOnPath(symPath,str,"syx",out,oldFile) END;

      ok := oldFile <> NIL;
      IF verbose IN modState THEN
	WriteString(out); output.writeChar(eol);
      END;
      IF ok THEN
	WITH bffStack[bffTop] DO
	  nextSb := 0;
	  length := (FLength.Length(oldFile) + 1023) DIV 1024 * 1024;
	  Storage.ALLOCATE(buffer,length);
	  ReadNBytes(oldFile,buffer,length,actual);
(*
StdError.WriteString("file <");
StdError.WriteString(str);
StdError.WriteString(">, flength = ");
StdError.WriteCard(actual,0);
StdError.WriteString(", buffer = ");
StdError.WriteCard(length,0);
StdError.WriteLn;
 *)
	  Assert((actual + 1023) DIV 1024 * 1024 = length);
	END;
	Close(oldFile,ok);
      END;
    END OpenOldSymFile;

    PROCEDURE ReadSb(VAR sb : SYSTEM.BYTE);
    (* reads a character from the sym-file stream *)
    BEGIN
      WITH bffStack[bffTop] DO
       (* $I- *)
	sb := buffer^[nextSb]; INC(nextSb);
       (* $I= *)
      END;
    END ReadSb;

    PROCEDURE CloseOldSymFile;
    BEGIN
      Storage.DEALLOCATE(bffStack[bffTop].buffer,bffStack[bffTop].length);
      DEC(bffTop);
    END CloseOldSymFile;

  BEGIN
    bffTop := 0;
    bffStack[0] := BuffDesc{0,0,NIL};
  END SymFileReader; (* ======================================= *)
 
(* --- symbol file writer procedures -------------------------- *)

  VAR key  : CARDINAL;

  PROCEDURE CreateNewSymFile(modHash : HashBucketType);
    VAR str : FileNameString;
	ix : CARDINAL;
  BEGIN
    key := 0;
    ix  := 0; (* could load library name here *)
    GetFileName(modHash,str,ix);
    GpCreateFile(str,"syx",str,auxFile);
    IF auxFile = NIL THEN AbortMessage("Can't create symbol file");
    ELSIF verbose IN modState THEN
      WriteString('Creating symbol file "');
      WriteString(str); output.writeChar('"'); output.writeChar(eol);
    END;
  END CreateNewSymFile;

  PROCEDURE WriteSb(sb : SYSTEM.BYTE);
  BEGIN
    WriteByte(auxFile,sb);
    (*$T-*)
    key := key * 2 + ORD(SYSTEM.CAST(CHAR,sb)) + 
			ORD(SYSTEM.CAST(INTEGER,key) < 0);
    (*$T=*)
  END WriteSb;

  PROCEDURE WriteSymbolKey();
    VAR ix : CARDINAL;
  BEGIN
    FOR ix := 1 TO bytesInWord DO
      WriteByte(auxFile,CHR(key MOD 400B)); key := key DIV 400B;
    END;
  END WriteSymbolKey;

  PROCEDURE ListKey(modName : HashBucketType;
		    keyValu : CARDINAL);
    CONST prefix = "      -- mod <";
    VAR ix : CARDINAL;
	str : ARRAY [0 .. 79] OF CHAR;

    PROCEDURE WrtNum(val : CARDINAL);
    BEGIN
      IF val > 10 THEN WrtNum(val DIV 10) END;
      output.writeChar(CHR(val MOD 10 + ORD("0")));
    END WrtNum;

  BEGIN
    str := prefix; ix := LENGTH(prefix);
    GetFileName(modName,str,ix);
    str[ix] := ">"; INC(ix);
    str[ix] := "";
    WriteString(str);
    WriteString(" key = ");
    WrtNum(keyValu);
    output.writeChar(eol);
  END ListKey;
      
  PROCEDURE CloseNewSymFile();
    VAR ok : BOOLEAN;
  BEGIN
    Close(auxFile,ok);
  END CloseNewSymFile;

(* --- reference file procedures ------------------------------ *)

  PROCEDURE CreateRefFile(modHash : HashBucketType);
    VAR str : FileNameString;
	ix : CARDINAL; ok : BOOLEAN;
  BEGIN
    ix := 0;
    IF useFilNm THEN
      str := inpName;
      WHILE (str[ix] <> nul) AND (str[ix] <> ".") DO INC(ix) END;
      Create(auxFile,str,ok);
    ELSE
      GetFileName(modHash,str,ix);
      GpCreateFile(str,"rfx",str,auxFile);
      ok := auxFile <> NIL;
    END;
    IF NOT ok THEN AbortMessage("Can't create reference file") END;
  END CreateRefFile;

  PROCEDURE WriteRb(rb : SYSTEM.BYTE);
  BEGIN
    WriteByte(auxFile,rb);
  END WriteRb;

  PROCEDURE CloseRefFile();
    VAR ok : BOOLEAN;
  BEGIN
    Close(auxFile,ok);
  END CloseRefFile;

(* --- object file procedures --------------------------------- *)

  PROCEDURE CreateObjFile(modHash : HashBucketType);
    VAR ix, nx : CARDINAL; ok : BOOLEAN;
	str : FileNameString;
	src : FileNameString;
  BEGIN
    ix := 0;
    IF useFilNm THEN 
      IF progMod IN modState THEN
	AbortMessage("-f option illegal for main module");
      END;
      str := inpName;
      WHILE (str[ix] <> nul) AND (str[ix] <> ".") DO INC(ix) END;
    ELSE
      GetFileName(modHash,str,ix);
    END;
    IF emitCil IN modState THEN
      GpCreateFile(str,"il",src,outFile);  (* src is actual name *)
    ELSE
      GpCreateFile(str,"dcf",src,outFile);  (* src is actual name *)
    END;
    IF outFile = NIL THEN AbortMessage("can't create obj file") END;
    Create(tmpFile,tmpName,ok);
    IF NOT ok THEN AbortMessage("can't create tmp file") END;
    nx := 0;
    REPEAT WriteByte(tmpFile,src[nx]); INC(nx) UNTIL src[nx] = "";
    Close(tmpFile,ok);
    IF verbose IN modState THEN
      src[ix] := nul; (* in case name was shortened *)
      WriteString('Output name is "'); WriteString(src);
      output.writeChar('"'); output.writeChar(eol);
    END;
  END CreateObjFile;

  PROCEDURE CloseObjFile();
    VAR ok : BOOLEAN;
  BEGIN
    Close(outFile,ok);
  END CloseObjFile;

  PROCEDURE WriteObjString(str : ARRAY OF CHAR);
    VAR ix : CARDINAL;
  BEGIN
    ix := 0;
    WHILE (ix <= HIGH(str)) AND
	  (str[ix] <> "") DO WriteObjByte(str[ix]); INC(ix) END;
  END WriteObjString;

  PROCEDURE EmitFileName(str : ARRAY OF CHAR);
  BEGIN
    WriteObjString(str);
    WriteObjByte('"');
    WriteObjString(inpName);
    WriteObjByte('"');
    WriteObjByte(eol);
  END EmitFileName;

  PROCEDURE WriteObjByte(ob : SYSTEM.BYTE);
  BEGIN
    WriteByte(outFile,ob);
  END WriteObjByte;

(* --- procedure for linking to editor ------------------------ *)

  PROCEDURE WriteExCommand(str : ARRAY OF CHAR);
    VAR ok : BOOLEAN; nx : CARDINAL;
  BEGIN
(*
StdError.WriteString("tmpName = ");
StdError.WriteString(tmpName);
StdError.WriteLn;
StdError.WriteString("message = ");
StdError.WriteString(str);
StdError.WriteLn;
 *)
    Create(tmpFile,tmpName,ok);
    IF NOT ok THEN AbortMessage("can't create tmp file") END;
    FOR nx := 0 TO HIGH(str) DO WriteByte(tmpFile,str[nx]) END;
    Close(tmpFile,ok);
  END WriteExCommand;

(* --- error reporting procedures ----------------------------- *)

  (*=============================================*)
  (* This module uses the procedures exported    *)
  (* from ListingControl to produce diagnostics  *)
  (* on the terminal, and embedded in the        *)
  (* listing file, if that has been requested.   *)
  (* The record "output" is assigned the proc-   *)
  (* variables which will perform writing to     *)
  (* either or both of the output destinations.  *)
  (*=============================================*)

  MODULE ErrorHandler;
  IMPORT Position, StdError, InOut, ResetInput, ReadCh, GetSourceRep,
	 CurrentFlags, nul, eol, CharSet, linePos, lineNum, inFile, 
	 SetFlagOn, Flags,
	 output, Number, WriteString, InitSkip, interactive,
	 GetErrList, ModStateFlags, modState, 
	 explain, explainAll, Explain, ExplainMore, StillMore,
	 EndListing, SetPos, GetPos, inpName, savOut, SetTermOnly,
	 WriteExCommand, ProgArgs;

  EXPORT ReportErrors, Report, Include;

    CONST max    = 25;
	  wMax   = max - 5; (* warnings stop before table is full *)

    TYPE  EEntry = RECORD
	             errNum : CARDINAL;
	             filPos : Position;
	           END;

    VAR   errors : ARRAY [0..max] OF EEntry;
	  hi     : CARDINAL; (* high-tide of array *)
 
    TYPE Writer = PROCEDURE (CARDINAL, ARRAY OF CHAR);
	          (* allows different styles of message *)

    PROCEDURE WriteNextLine();
      VAR ch : CHAR;
    BEGIN
      Number(lineNum); WriteString("   ");
      LOOP
	ReadCh(ch);
	IF (ch = eol) OR (ch = nul) THEN EXIT END;
	output.writeChar(ch);
      END;
      output.writeChar(eol); 
    END WriteNextLine;

    (* ============================================ *)
	MODULE Interact;
	  IMPORT errors, ResetInput, GetPos, SetPos, 
		 Report, explainAll, ExplainMore, StillMore, nul, eol, CharSet,
		 InitSkip, WriteNextLine, inFile, output, savOut,
		 StdError, InOut, linePos, lineNum, Position, GetErrList,
		 SetTermOnly, WriteExCommand, ProgArgs, inpName;
	  EXPORT Query;

	  (* ========================================= *)
	  CONST nLns = 3; (* number of lines displayed *)
	  (* ========================================= *)

	  VAR filePtrSav, skipPtrSav : CARDINAL;
	      linePosSav, skipPosSav : CARDINAL;
	      lineNumSav, skipNumSav : CARDINAL;

	  VAR initialized : BOOLEAN;
	      rch : CHAR;

	  CONST str = 
'<newline> to proceed, "m" for more info, "v" to go to editor, "q" to quit : ';
		noMore = "... no more information on this error";

	  PROCEDURE SavePos;
	  BEGIN
	    GetPos(inFile,filePtrSav); 
	    linePosSav := linePos;
	    lineNumSav := lineNum;
	    IF NOT initialized THEN 
	      ResetInput(); InitSkip(); 
	      GetErrList();
	      initialized := TRUE;
	    ELSE
	      lineNum := skipNumSav;
	      linePos := skipPosSav;
	      SetPos(inFile,skipPtrSav);
	    END;
	  END SavePos;

	  PROCEDURE Restore;
	  BEGIN
	    GetPos(inFile,skipPtrSav);
	    skipPosSav := linePos;
	    skipNumSav := lineNum;
	    SetPos(inFile,filePtrSav);
	    linePos := linePosSav;
	    lineNum := lineNumSav;
	  END Restore;

	  PROCEDURE Query(ix : CARDINAL);
	    VAR targetLine : CARDINAL;
		num : ARRAY [0 .. 7] OF CHAR; 
		nx    : CARDINAL;
	        start : CARDINAL;
		done  : BOOLEAN;

		PROCEDURE BuildNum(n : CARDINAL);
		BEGIN
		  IF n = 0 THEN RETURN;
		  ELSIF n > 9 THEN BuildNum(n DIV 10);
		  END;
		  num[nx] := CHR(n MOD 10 + ORD("0"));
		  INC(nx);
		END BuildNum;

	  BEGIN
	    savOut := output; SetTermOnly;
	    SavePos();
	    targetLine := errors[ix].filPos.line;
	    (*
	     *	after writing out a previous error message
	     *	lineNum = old(targetLine) + 1, thus >= necessary
	     *	and sufficient to prevent multiple copies
	     *)
	    IF targetLine >= lineNum THEN
	      IF targetLine - lineNum <= nLns THEN 
		start := lineNum;
	      ELSE start := targetLine - nLns;
	      END;
	      output.skipLines(start);
	      FOR start:= lineNum TO targetLine DO WriteNextLine() END;
	    END;
	    done := FALSE;
	    Report(ix);
	    LOOP
	      StdError.WriteString(str);
	      REPEAT
	        InOut.Read(rch);
	      UNTIL rch IN CharSet{'v','e','m','q', eol};
	      IF rch IN CharSet{"v","e"} THEN 
	        num[0] := "+"; nx := 1;
	        BuildNum(targetLine); num[nx] := nul;
	        WriteExCommand(num);
	        ProgArgs.UNIXexit(3);
	      ELSIF rch = "m" THEN 
		InOut.WriteLn;
		IF done THEN
		  StdError.WriteString(noMore);
		  InOut.WriteLn; 
		ELSE
		  IF NOT explainAll THEN ExplainMore() END;
		  StillMore();
		  done := TRUE;
	        END;
	      ELSIF rch = "q" THEN 
		InOut.WriteLn; ProgArgs.UNIXexit(4);
	      ELSE 
		EXIT; (* ==> go to next error, if any *)
	      END;
	    END;
	    InOut.WriteLn;
	    Restore;
	    output := savOut;
	  END Query;

	BEGIN
	  initialized := FALSE;
	END Interact;
    (* ============================================ *)


    PROCEDURE Include(ordErr, nr : CARDINAL; filPos : Position);
    BEGIN
      IF    ordErr < 100 THEN SetFlagOn(lexErrors);
      ELSIF ordErr < 200 THEN SetFlagOn(synErrors);
      ELSIF ordErr < 450 THEN SetFlagOn(semErrors);
      ELSE  (* >= 450 *)  SetFlagOn(warnings);
      END;
      IF (hi < wMax) OR ((hi < max) AND (ordErr < 450)) THEN
	errors[hi].errNum := nr;
	errors[hi].filPos := filPos;
	INC(hi);
      END;
      IF interactive AND (ordErr < 450) THEN Query(hi - 1) END;
    END Include;

    PROCEDURE WritePosition(tab : CARDINAL;
	                    str : ARRAY OF CHAR);
      CONST fold = 24;
      VAR   ix   : CARDINAL; onRight : BOOLEAN;
    BEGIN
      WriteString(" ****   ");
      onRight := errors[tab].filPos.pos <= fold;
	(* 8 changed to 7 on next line to suit new HIGH rules *)
      IF onRight THEN ix := 2 ELSE ix := HIGH(str) + 7 END; (* 10-Feb-92 *)
      FOR ix := ix TO errors[tab].filPos.pos DO
	output.writeChar('.');
      END;
      IF onRight THEN output.writeChar('^') END;
      WriteString(str);
      Number(errors[tab].errNum);
      IF NOT onRight THEN output.writeChar('^') END;
      output.writeChar(eol);
      (* ! and diagnostic? *)
    END WritePosition;

    PROCEDURE WriteMessage(tab : CARDINAL;
	                   str : ARRAY OF CHAR);
      VAR rep : ARRAY [0..39] OF CHAR; ix : CARDINAL;
    BEGIN
      WriteString(" **** ");
      WriteString(str);
      Number(errors[tab].errNum);
      WriteString(" with ident <"); ix := 0;
      GetSourceRep(errors[tab].filPos.pos,rep,ix);
      IF ix < 39 THEN
	rep[ix] := '>'; INC(ix); rep[ix] := nul;
      END;
      WriteString(rep); output.writeChar(eol);
      (* ! and diagnostic? *)
    END WriteMessage;

    PROCEDURE Report(ix : CARDINAL);
      VAR writeErr : Writer;
    BEGIN
      WITH errors[ix] DO
	IF errNum > 1000 THEN
	  DEC(errNum,1000);
	  writeErr := WriteMessage;
	ELSE writeErr := WritePosition;
	END;
	IF    errNum < 100 THEN writeErr(ix,' Lexical Error #');
	ELSIF errNum < 200 THEN writeErr(ix,' Syntax Error #');
	ELSIF errNum < 450 THEN writeErr(ix,' SemanticError #');
	ELSE  (* ==> warning *) writeErr(ix,' Warning #');
	END;
	IF explain THEN Explain(errNum) END;
	IF explainAll THEN ExplainMore() END;
      END;
    END Report;

    PROCEDURE ReportErrors();
    (* error entries are _almost_ in line order. the *)
    (* exception is warnings found during parsing, & *)
    (* static semantic errors found during traversal *)
      VAR nexLn, tabIx : CARDINAL;
	  writeIt, ok : BOOLEAN;

	PROCEDURE SortTable;
	  VAR clean : BOOLEAN; temp :EEntry;
	      top, ix : CARDINAL;
	BEGIN (* bubble ok when nearly sorted already *)
	  IF hi < 2 THEN RETURN END;
	  FOR top := hi - 1 TO 1 BY -1 DO
	    clean := TRUE;
	    FOR ix := 0 TO top - 1 DO
	      IF errors[ix].filPos.line > errors[ix+1].filPos.line THEN
	        temp := errors[ix];
	        errors[ix] := errors[ix+1];
	        errors[ix+1] := temp;
	        clean := FALSE;
	      END;
	    END;
	    IF clean THEN RETURN END;
	  END;
	END SortTable;

    (*
     *  Boolean writeIt is used to suppress warning messages in
     *  the case that gpm -d was used, but _errors_ arose (kjg)
     *)
    BEGIN
      IF interactive AND NOT(listings IN CurrentFlags()) THEN RETURN END;
      SortTable; (* just in case *)
      ResetInput(); tabIx := 0; InitSkip();
      IF (hi > 0) AND explain THEN 
	GetErrList();
	IF NOT explain THEN explainAll := FALSE END;
      END;
      WHILE tabIx < hi DO (* get next batch of errors *)
	nexLn := errors[tabIx].filPos.line;
	output.skipLines(nexLn);
	writeIt := NOT (dangerous IN modState) OR
			 (errors[tabIx].errNum MOD 1000 < 450);
	IF writeIt THEN WriteNextLine() END;
	REPEAT (* write out error *)
	  IF writeIt THEN Report(tabIx) END;
	  IF errors[tabIx].errNum = 3 THEN RETURN END; 
	  (* file ends inside comment *)
	  INC(tabIx);
	UNTIL (tabIx = hi) OR (errors[tabIx].filPos.line > nexLn);
      END;
      IF listings IN CurrentFlags() THEN EndListing() END;
    END ReportErrors;

  BEGIN
    hi := 0;
  END ErrorHandler;
  (*=============================================*)

  PROCEDURE Error(nr : CARDINAL);
  BEGIN
    IF  (nr >= 450) AND (dangerous IN modState) THEN RETURN;
    ELSIF  (nr >= 200) OR IsSynchronized() THEN
      Include(nr,nr,lastPos);
      IF nr < 200 THEN StartSyncCount() END;
    END;
  END Error;

  PROCEDURE ErrIdent(nr : CARDINAL; id : HashBucketType);
  (* these errors have a line no and hash index, but no position *)
  (* ==> nr > 1000 tags the different meaning of the pos field   *)
    VAR dummy : Position;
  BEGIN
    IF  (nr >= 450) AND (dangerous IN modState) THEN RETURN END;
    dummy.line := lastPos.line;
    dummy.pos  := id;
    Include(nr,(nr + 1000),dummy);
  END ErrIdent;

(* --- abort procedures --------------------------------------- *)

  PROCEDURE AbortMessage(str : ARRAY OF CHAR);
  (* outputs message to stdErr stream and aborts *)
  BEGIN
    StdError.WriteString('#gpmx: ');
    StdError.WriteString(str); StdError.WriteLn();
    StdError.WriteString("Aborting ... ");
    StdError.WriteLn; ProgArgs.UNIXexit(4);
  END AbortMessage;

  PROCEDURE SymbolMessage(expected : TerminalSymbols;
	                  found    : TerminalSymbols);
  (* outputs message to stdErr stream and aborts.
     Used for unrecoverable errors in a symbol input file  *)
  BEGIN
    StdError.WriteString("Expected ");
    StdError.WriteCard(ORD(expected),0);
    StdError.WriteString(" - found ");
    StdError.WriteCard(ORD(found),0);
    StdError.WriteLn; ProgArgs.UNIXexit(4);
  END SymbolMessage;

BEGIN
  debugOn := FALSE;
  EnvironString("M2SYM", symPath);
  EnvironString("CLRSYM", clrPath);
  EnvironString("EXTENDGPM", extend);
  EnvironString("OS", osString);
END M2InOut.   

