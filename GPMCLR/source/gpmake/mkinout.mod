(*
 * =========== macro processed output from MPP  ==========
 *
 * input file  : mkinout.mpp
 * time stamp  : 2004:01:08::03:43:36
 *
 * output file : mkinout.mod
 * created at  : 2004:01:12::14:21:43
 *
 * options ... :  /Ddotnet86
 *
 * =======================================================
 *)

(* -- RCS header --
	$Log:	mkinout.mpp,v $
Revision 1.2  93/11/03  09:00:57  mboss
Added DEC Alpha changes.

Revision 1.1  93/03/25  14:31:55  mboss
Initial revision

*)
(* 
 *  extracted with 
 * 	    "opsys" == "windows"
 * 	   "endian" == "little"
 *	"processor" == "iap386"
 *)

(*
 *  EDITED FOR GPM-PC ... from M2InOut -Ddecmips
 *)

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
(*								*)
(*               CUT DOWN VERSION FOR PC GPMAKE                 *)
(*                     dwc September 1991                       *)
(*                                                              *)
(*			  : 00-Feb-92  kjg move back to UNIX    *)
(*			  : 16-Mar-92  jrh guard getArg call	*)
(*			  : 20-Mar-92  kjg move M2SYM fetch to  *)
(*			     init. for progs that don't OpenInp *)
(*			     Use arg0 for abort message ...	*)
(*			  : 30-Apr-92  jrh add gpm options arg	*)
(*					   check EnvironString	*)
(*			  : 24-Jun-92  jrh filename length limit*)
(*                        : 03-Aug-92  kjg use GpFiles library  *)
(*			  : 27-Nov-92  kjg remove unused "ok's" *)
(*                        : 28-Oct-93  pms Added Alpha changes  *)
(*                        : 08-Jan-04  kjg Added CLR changes    *)
(****************************************************************)




IMPLEMENTATION MODULE MkInOut;

  IMPORT SYSTEM, ProgArgs;
  FROM MkAlphabets IMPORT
        HashBucketType, TermSymbols, Flags,
        FlagSet, ModStateFlags, ModStateSet;
  FROM MkNameHandler IMPORT GetSourceRep;
  FROM UxFiles IMPORT
	File, Open, Create, Close, OpenMode,
        ReadByte, ReadNBytes, Reset, WriteByte,
	EndFile, GetPos, SetPos;
  FROM PathLookup IMPORT FindAndOpen;
  FROM Ascii IMPORT ht, lf, nul, cr;
  IMPORT StdError;
  FROM GpFiles IMPORT GpFindOnPath, GpCreateFile, GpFindLocal;
  FROM ProgArgs IMPORT 
	Assert, EnvironString, UNIXtime, VersionTime, ArgNumber, GetArg;

  (* ===================================================== *)
  (* ===================================================== *)
    CONST greetStr = "B-release of gpmake, unix version ";
  (* ===================================================== *)
  (* ===================================================== *)
  (* ===================================================== *)
  (*            Global types and variables                 *)
  (* ===================================================== *)

    CONST eol = lf;

    TYPE  
	  CharSet = SET OF CHAR;

    VAR   linePos  : CARDINAL;
          lineNum  : CARDINAL;

    VAR inFile,		(* input file -- .mod or .def  *)
        auxFile,	(* input and output .syx files *) 
        outFile, 	(* the object file for output  *)
	makFile : File; (* gpmake temporary file       *)

    VAR
           sBuff : ARRAY [0 .. 1023] OF SYSTEM.BYTE;
           sCount, sNumLeft : CARDINAL;
           tFileName  : FileNameString; (* arg[1] *)
	   inpName    : FileNameString; (* arg[2] == input name   *)
           baseName   : FileNameString; (* actual input file name *)
	   (* symPath was 1024, but graphbuild restricted it to 128/256 *)
           symPath    : MiddleString;	(* symFile path    *)
           clrPath    : MiddleString;	(* clrsyms path    *)
	   argOne     : MiddleString;
	   argStar    : MiddleString;

           explain    : BOOLEAN;
           clrTarget  : BOOLEAN;
           argNum     : CARDINAL;

  (*=============================================*)

  (*=============================================*)
	PROCEDURE DiagName(nam : HashBucketType);
	VAR str : ARRAY [0 .. 127] OF CHAR;
	    index : CARDINAL;
	BEGIN
	  index := 0;
	  GetSourceRep(nam,str,index);
	  StdError.WriteString(str);
	END DiagName;
  (*=============================================*)
        PROCEDURE OpenMessage(s1,s2 : ARRAY OF CHAR);
        BEGIN
          StdError.WriteString(s1);
          StdError.WriteString(" <");
          StdError.WriteString(s2);
          StdError.Write(">");
          StdError.WriteLn;
        END OpenMessage;
  (*=============================================*)
        PROCEDURE GetOptions();
          VAR index : CARDINAL;
              jndex : CARDINAL;
              chr   : CHAR;
        BEGIN
          FOR index := 1 TO argNum-1 DO
            GetArg(index, argStar);
            IF argStar[0] = "-" THEN
              FOR jndex := 1 TO LENGTH(argStar)-1 DO
                chr := argStar[jndex];
                IF    chr = "+" THEN explain   := TRUE;
                ELSIF chr = "c" THEN clrTarget := TRUE;
                ELSIF chr = "m" THEN clrTarget := TRUE;
                END;
              END;
            END;
          END;
        END GetOptions;
  (*=============================================*)

(* --- main input file procedures ----------------------------- *)

  PROCEDURE OpenInput;
  (* in case of errors, lexErrors is set in flags *)
    VAR ix  : FileNameIndex;
        ext : ARRAY [0 .. 3] OF CHAR;
  BEGIN
   (*  Call is
    *  from graphbuild  with args graphbuild tempFile gpmOptionString baseStem
    *  or   gpscript    with args gpscript {gpmOption} baseStem ;
    *  baseStem is module[.mod]
    *)
    GetArg(ArgNumber() - 1,inpName); (* base module/file name *)
    Assert (inpName[0] <> "-");
    (*
     *  check if name has a dot in it
     *)
    ix := 0;
    WHILE (inpName[ix] <> ".") AND (inpName[ix] <> "") DO INC(ix) END;
    IF inpName[ix] = "" THEN ext := "mod";
    ELSE ext := "";
    END;
    GpFindLocal(inpName,ext,baseName,inFile);
    IF inFile = NIL THEN
      AbortMessage("can't open input file: ",inpName);
    ELSIF explain THEN
      OpenMessage("Opened", baseName);
    END;
  END OpenInput;

  PROCEDURE BaseName(VAR name : ARRAY OF CHAR);
    VAR index : CARDINAL;
  BEGIN
    FOR index := 0 TO HIGH(name) DO name[index] := baseName[index] END;
  END BaseName;

  PROCEDURE SetAppName(name : ARRAY OF CHAR);
    VAR index : CARDINAL;
  BEGIN
    FOR index := 0 TO HIGH(name) DO argOne[index] := name[index] END;
  END SetAppName;

  PROCEDURE OpenDefOrModFile (name : ARRAY OF CHAR);
  VAR
    new : FileNameString;
  BEGIN
    GpFindLocal(name,"",new,inFile);
    IF inFile = NIL THEN
      StdError.WriteString("Local *.def must have LOCAL *.mod file");
      StdError.WriteLn();
      AbortMessage("file not found: ",name);
    ELSIF explain THEN
      OpenMessage("Opened", new);
    END;
  END OpenDefOrModFile;

  PROCEDURE CloseDefOrModFile;
  VAR
    done : BOOLEAN;
  BEGIN
    IF inFile <> NIL THEN Close(inFile,done) END;
  END CloseDefOrModFile;

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

(* --- symbol file procedures --------------------------------- *)

  PROCEDURE OpenSymFile(modHash : HashBucketType;
		        VAR out : MiddleString;
                        VAR  ok : BOOLEAN);
    VAR str : FileNameString; 
	new : MiddleString; 
	ix : CARDINAL;
  BEGIN
    ix := 0; 
    ok := FALSE;
    GetSourceRep(modHash,str,ix);
    GpFindLocal(str,"syx",out,auxFile);
    ok := auxFile <> NIL;
    IF explain AND ok THEN 
      StdError.WriteString("Opened "); 
      StdError.WriteString(out);
      StdError.WriteString(" from current directory"); 
      StdError.WriteLn;
    END;
    IF NOT ok AND clrTarget THEN
      GpFindOnPath(clrPath,str,"syx",out,auxFile);
      ok := auxFile <> NIL;
      IF explain AND ok THEN 
        StdError.WriteString("Opened "); 
        StdError.WriteString(out);
        StdError.WriteString(" from CLRSYM path"); 
        StdError.WriteLn;
      END;
    END;
    IF NOT ok THEN
      GpFindOnPath(symPath,str,"syx",out,auxFile);
      ok := auxFile <> NIL;
      IF explain AND ok THEN 
        StdError.WriteString("Opened "); 
        StdError.WriteString(out);
        StdError.WriteString(" from M2SYM path"); 
        StdError.WriteLn;
      END;
    END;
  END OpenSymFile;

  PROCEDURE ReadSb(VAR sb : SYSTEM.BYTE);
  (* reads a character from the sym-file stream *)
  BEGIN
    IF sCount >= sNumLeft THEN
      ReadNBytes(auxFile,SYSTEM.ADR(sBuff),1024,sNumLeft);
      sCount := 0;
    END;
    sb := sBuff[sCount]; INC(sCount);
  END ReadSb;

  PROCEDURE CloseSymFile();
    VAR ok : BOOLEAN;
  BEGIN
    IF auxFile <> NIL THEN Close(auxFile,ok) END;
  END CloseSymFile;

(* --- make file procedures ----------------------------------- *)

  PROCEDURE OpenMakFile;
  VAR
    ok : BOOLEAN;
    nam : FileNameString;
  BEGIN
    (* Call is from decider; name is module.mak *)
    GetArg(argNum-1, inpName);

   (*
    *  This call does not use the GpFind... procs
    *  as the openmode is not ReadOnly (kjg Aug-92)
    *  So -- open it to find the correct name,
    *  then open it with the correct mode.
    *)
    GpFindLocal(inpName,"",nam,makFile);
    IF makFile <> NIL THEN Close(makFile,ok) END;
    Open(makFile,nam,ReadWrite,ok);
    IF NOT ok THEN
      AbortMessage("can't open make file: ",inpName);
    ELSIF explain THEN
      OpenMessage("Opened", nam);
    END;
  END OpenMakFile;

  PROCEDURE CreateMakFile (makName : ARRAY OF CHAR);
  VAR
    done : BOOLEAN;
  BEGIN
    GpCreateFile(makName,"",makName,makFile);
    IF makFile = NIL THEN
      AbortMessage("can't create make file: ",makName);
    ELSIF explain THEN
      OpenMessage("Created", makName);
    END;
  END CreateMakFile;
  
  PROCEDURE CloseMakFile;
  VAR
    done : BOOLEAN;
  BEGIN
    IF makFile <> NIL THEN Close(makFile,done) END;
  END CloseMakFile;
  
  PROCEDURE GetMakSymPos() : CARDINAL;
  VAR
    pos : CARDINAL;
  BEGIN
    GetPos(makFile,pos);
    RETURN (pos - 1);       (* want position of symbol - always one *)
  END GetMakSymPos;         (* byte past symbol   *)     
  
  PROCEDURE GetMakFilePos() : CARDINAL;
  VAR
    pos : CARDINAL;
  BEGIN
    GetPos(makFile,pos);
    RETURN (pos);            (* want actual file position - not symbol *)
  END GetMakFilePos;

  PROCEDURE SetMakFilePos(pos : CARDINAL);
  BEGIN
    SetPos(makFile,pos);
  END SetMakFilePos;

  PROCEDURE WriteMakString (str : ARRAY OF CHAR);
  VAR
    i : CARDINAL;
  BEGIN
    i := 0;
    WHILE (i <= HIGH(str)) AND (str[i] <> nul) DO
      WriteByte(makFile,str[i]);
      INC(i);
    END;
    WriteByte(makFile,nul); (* nul byte string terminator *)
  END WriteMakString; 
  
  PROCEDURE WriteMakKey (key : CARDINAL);
    VAR crd8 : [0 .. 255];
  BEGIN
    crd8 := key MOD 256; key := key DIV 256; 
    WriteByte(makFile,crd8);
    crd8 := key MOD 256; key := key DIV 256; 
    WriteByte(makFile,crd8);
    crd8 := key MOD 256; key := key DIV 256; 
    WriteByte(makFile,crd8);
    crd8 := key MOD 256;
    WriteByte(makFile,crd8);
  END WriteMakKey; 
  
  PROCEDURE ReadMb (VAR byte : SYSTEM.BYTE);
  BEGIN
    ReadByte(makFile,byte);
  END ReadMb;

  PROCEDURE WriteMb (byte : SYSTEM.BYTE);
  BEGIN
    WriteByte(makFile,byte);
  END WriteMb;

  PROCEDURE WriteStringToTempFile (str : ARRAY OF CHAR);
  VAR
    i : CARDINAL;
    tFile : File;
    ok : BOOLEAN;
  BEGIN
    Create(tFile,tFileName,ok);
    IF NOT ok THEN
      AbortMessage("can't create temporary file: ",tFileName);
    ELSE
      IF explain THEN 
        StdError.WriteString("Created tempfile ");
        StdError.WriteString(tFileName); 
        StdError.WriteString(' with data "');
        StdError.WriteString(str); 
        StdError.Write('"'); 
        StdError.WriteLn;
      END;
      i := 0;
      WHILE (str[i] <> nul) AND (i <= HIGH(str)) DO
        WriteByte(tFile,str[i]);
        INC(i);
      END;
      WriteByte(tFile,nul);
      Close(tFile,ok);
    END;
  END WriteStringToTempFile;

  PROCEDURE ReadStringFromTempFile (VAR str : ARRAY OF CHAR);
  VAR
    i : CARDINAL;
    tFile : File;
    ok : BOOLEAN;
  BEGIN
    Open(tFile,tFileName,ReadOnly,ok);
    IF NOT ok THEN
      AbortMessage("can't open temporary file: ",tFileName);
    ELSE
      IF explain THEN OpenMessage("Opened", tFileName) END;
      i := 0;
      ReadByte(tFile,str[i]);
      WHILE (str[i] <> nul) AND (i <= HIGH(str)) DO
	INC(i);
	ReadByte(tFile,str[i]);
      END;
      Close(tFile,ok);
    END;
  END ReadStringFromTempFile;

(* --- reference file procedures ------------------------------ *)

  PROCEDURE OpenRefFile(modHash : HashBucketType;
                        VAR new : MiddleString;
                        VAR ok  : BOOLEAN);
    VAR str : FileNameString;
        ix  : CARDINAL;
  BEGIN
    ix := 0;
    GetSourceRep(modHash,str,ix);
    GpFindLocal(str,"rfx",new,auxFile);
    ok := auxFile <> NIL;
    IF explain AND ok THEN OpenMessage("Opened", new) END;
  END OpenRefFile;

  PROCEDURE CloseRefFile();
    VAR ok : BOOLEAN;
  BEGIN
    IF auxFile <> NIL THEN Close(auxFile,ok) END;
  END CloseRefFile;

(* --- abort procedures --------------------------------------- *)

  PROCEDURE AbortMessage(str1 : ARRAY OF CHAR;
			 str2 : ARRAY OF CHAR);
  (* outputs message to stdErr stream and aborts *)
  BEGIN
    StdError.Write("#");
    StdError.WriteString(argOne);
    StdError.WriteString(": ");
    StdError.WriteString(str1);
    StdError.WriteString(str2); StdError.WriteLn();
    StdError.WriteString("Aborting ... ");
    StdError.WriteLn; ProgArgs.UNIXexit(2);
  END AbortMessage;

BEGIN
  argNum    := ArgNumber();
  explain   := FALSE;
  clrTarget := FALSE;

  IF argNum > 0 THEN
    GetArg(0,tFileName);
    IF argNum > 1 THEN GetOptions() END;
  (* ELSE GPScript main will give usage message and abort *)
  END;

  symPath[middleMax] := nul;
  clrPath[middleMax] := nul;
  EnvironString("M2SYM",  symPath);
  EnvironString("CLRSYM", clrPath);
  IF symPath[middleMax] <> nul THEN AbortMessage("M2SYM path too long","") END;
  IF clrPath[middleMax] <> nul THEN AbortMessage("CLRSYM path too long","") END;
  debugOn := FALSE;
  sCount  := 0;
  sNumLeft := 0;
END MkInOut.   
