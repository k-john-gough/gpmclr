(*
 * =========== macro processed output from MPP  ==========
 *
 * input file  : gpmake.mpp
 * time stamp  : 2004:01:08::10:01:20
 *
 * output file : gpmake.mod
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
(*                Modula-2 Compiler Source Module               *)
(*                                                              *)
(*                The Make Facility - PC Version                *)
(*                       Driver Program                         *)
(*                                                              *)
(*      This program forks the program graphbuild which         *)
(*      builds the calls graph which is flattened and written   *)
(*      to the file with the extension .mak.  The name of this  *)
(*      file is returned to this program via the file modbase.  *)
(*      This driver program then continuously forks a decider   *)
(*      decider process which reads/updates the .mak file and   *)
(*      calls the compiler when required.  When all the modules *)
(*      which need recompilation have been completed the build  *)
(*      process is invoked.                                     *)
(*                                                              *)
(*      original module : dwc October 1991			*)
(*      modifications   : kjg Nov 91 use pc version of PcProcs  *)
(*			: kjg Nov 91 modified error messages	*)
(*			: kjg Feb 92 modified for unix lib'ries *)
(*			: kjg Mar 92 return error in Spawnv	*)
(*				     larger string sizes	*)
(*			: jrh Apr 92 check EnvironString	*)
(*			: jrh Jun 92 gpm args one arg on pc too	*)
(*                      : kjg Sep 92 uses new GpFiles procs     *)
(*                      : jrh Dec 92 correct case for Delete    *)
(*                      : jrh Jun 93 Decider return code 3 ok   *)
(*                      : pms Nov 93 Increase filename length   *)
(*                                   for pc version             *)
(*                      : kjg Nov 03 Version for the CLR        *)
(*                                                              *)
(****************************************************************)






MODULE GPMake;

IMPORT StdError;
FROM SYSTEM IMPORT ADDRESS, CAST;
FROM PcProcesses IMPORT Spawnv, PSP;
FROM Ascii      IMPORT nul;
FROM Types      IMPORT Int32;
FROM PathLookup IMPORT FindAbsName;
FROM BuildArgs  IMPORT ArgPtr, Arg2, Arg3, Arg4, ArgBlock,
		       ArgsOf, NewArgBlock, AppendArg;
FROM ProgArgs   IMPORT ArgNumber, GetArg, UNIXexit, EnvironString;
FROM UxFiles    IMPORT ReadByte, Open, Delete, File, ReadOnly, Close;
FROM GpFiles    IMPORT GpFilename;
(*
 *  Instead of:
 * FROM MkInOut IMPORT
 *	longMax, LongString, MiddleString, ShortString, FileNameString;
 *  copy constant & type declarations to avoid linking MkInOut:
*)
  CONST
    longMax = 4095;	(* Upper bound of (very) long strings *)
    middleMax = 255;	(* Upper bound of middle-size strings -
			   $M2SYM & single path names *)
    shortMax = 50;	(* Upper bound of short strings - 
			   args, error messages *)
    fileNameMax = 84;	(* Upper bound of file names - 
			   identifier + extension *)

    GRAPHBUILD = "graphbld";
    DECIDER    = "decider";
    GPM        = "gpx";
    BUILD      = "build";

  TYPE
    LongIndex      = [0 .. longMax];
    MiddleIndex    = [0 .. middleMax];
    ShortIndex     = [0 .. shortMax];
    FileNameIndex  = [0 .. fileNameMax];
    LongString     = ARRAY LongIndex     OF CHAR;
    MiddleString   = ARRAY MiddleIndex   OF CHAR;
    ShortString    = ARRAY ShortIndex    OF CHAR;
    FileNameString = ARRAY FileNameIndex OF CHAR;

CONST
  usageStr = "Usage: GPMake [(-|/)+acdfgIilO[012]mprStvVX?] BaseModFileName";
  usage2   = "           -+ causes GPMake to chatter about progress";
  usage3   = "           -S (non CLR) calls build with Build -s";
  usage4   = "           -c creates CLR program executables";
  usage5   = "           -? gives this usage message";
  usage6   = "          ... other options are for GPM";
  loopMess = "Make must create obj-files, so -D and -n are illegal";
  clrMess  = "Make must create PE-files, so -cS and -mS are illegal";
  badRet   = "bad exit code from ";
  cantExec = "can't exec program ";

VAR
  options    : BOOLEAN;
  persistent : BOOLEAN;
  explain    : BOOLEAN;
  clrTarget  : BOOLEAN;
  hasWswitch : BOOLEAN;
  hasYswitch : BOOLEAN;
  result, compRes : INTEGER;
  argStr  : ShortString;
  gpmStr  : ShortString;
  errStr  : ShortString;
  pathStr : LongString;		(* the entire PATH environment variable *)
  absPath : MiddleString;	(* abs names of graphbuild, build *)
  decName : MiddleString;	(* abs of decider  *)
  gpmName : MiddleString;	(* abs name of gpm *)
  tFileName : ShortString;	(* abs name of tmp - in fact only 13 chars*)
  argN : CARDINAL;
  fName   : FileNameString;	(* file to compile or build, from decider *)
  makName : FileNameString;	(* make file name, from graphbuild        *)
  baseFileName : FileNameString;(* base name, from command line;          *
				 * note that mkinout.ShortenName          *
				 * assumes that there is no leading path  *
				 * string                                 *)
  gpmArgs, deciderArgs, graphBuildArgs : ArgPtr;
  bldArgs  : ArgBlock;

(*  =============================================
 *  the following procedures are inlined here to 
 *  minimize the size of the executable in memory
 *)

  PROCEDURE FormTmpNam();
    VAR   index, pid : CARDINAL;
    VAR   prefix : ShortString;
  BEGIN
    EnvironString("TEMP",prefix);
    index := LENGTH(prefix);
    IF (index > 0) AND (prefix[index-1] <> "\") THEN
      prefix[index] := "\";
      INC(index);
    END;
    prefix[index]   := "g"; prefix[index+1] := "p";
    prefix[index+2] := "m"; prefix[index+3] := "";
    pid := CAST(CARDINAL,PSP());
    tFileName := prefix;
    FOR index := LENGTH(prefix) + 4 TO LENGTH(prefix) BY -1 DO
      tFileName[index] := CHR(pid MOD 10 + ORD("0"));
      pid := pid DIV 10;
    END;
    tFileName[LENGTH(prefix) + 5] := "";
  END FormTmpNam;

  PROCEDURE AbortMessage(str1 : ARRAY OF CHAR;
			 str2 : ARRAY OF CHAR);
  (* outputs message to stdErr stream and aborts *)
  BEGIN
    DeleteTmpFile();
    StdError.WriteString('#gpmake: ');
    StdError.WriteString(str1);
    StdError.WriteString(str2); StdError.WriteLn();
    StdError.WriteString("Aborting ... ");
    StdError.WriteLn; 
    UNIXexit(2);
  END AbortMessage;

  PROCEDURE DeleteMakFile();
  VAR
    ok : BOOLEAN;
  BEGIN
    IF makName[0] <> "" THEN
      GpFilename(makName, "", makName);	(* force correct case *)
      Delete(makName,ok);
      IF explain AND ok THEN
        StdError.WriteString(makName);
        StdError.WriteString(" deleted"); StdError.WriteLn;
      END;
    END;
  END DeleteMakFile;

  PROCEDURE DeleteTmpFile();
  VAR
    ok : BOOLEAN;
  BEGIN
    IF tFileName[0] <> "" THEN
      Delete(tFileName,ok);
      IF explain AND ok THEN
        StdError.WriteString(tFileName);
        StdError.WriteString(" deleted"); StdError.WriteLn;
      END;
    END;
  END DeleteTmpFile;

  PROCEDURE UsageMessage();
  BEGIN
    StdError.WriteString('#GPMake: '); 
    StdError.WriteString(usageStr); StdError.WriteLn;
    StdError.WriteString(usage2); StdError.WriteLn;
    StdError.WriteString(usage3); StdError.WriteLn;
    StdError.WriteString(usage4); StdError.WriteLn;
    StdError.WriteString(usage5); StdError.WriteLn;
    StdError.WriteString(usage6); StdError.WriteLn;
  END UsageMessage;

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
      i := 0;
      ReadByte(tFile,str[i]);
      WHILE (str[i] <> nul) AND (i <= HIGH(str)) DO
	INC(i);
	ReadByte(tFile,str[i]);
      END;
      Close(tFile,ok);
    END;
(*
 *  ErrOutput.WriteString("message ");
 *  ErrOutput.WriteString(str);
 *  ErrOutput.WriteLn;
 *)
  END ReadStringFromTempFile;

(*  ============================================= *)


  PROCEDURE GetGpmOptions(VAR options : BOOLEAN; 
                          VAR argNo   : CARDINAL; 
		          VAR myArgs  : ARRAY OF CHAR;
		          VAR gpArgs  : ARRAY OF CHAR);
  (* post:  gpArgs contains a string of options to gpm, argNo is the 
   *        argument number of the module name, options is the number
   *        of options. myArgs is the arg string to Decider etc.
   *)
  VAR
    strIx, optIx : CARDINAL; 
    arg          : ShortString;
    ch           : CHAR;
    numOfArgs    : CARDINAL;
  BEGIN
    numOfArgs := ArgNumber();
    IF numOfArgs = 0 THEN AbortMessage(usageStr,""); END;
    argNo := 0;
    optIx := 0;
    GetArg(argNo,arg);
    IF arg[0] = '-' THEN 
      myArgs[0] := "-"; gpArgs[0] := "-"; INC(optIx);
    ELSIF arg[0] = '/' THEN 
      myArgs[0] := "-"; gpArgs[0] := "-"; INC(optIx); 
    END;
    WHILE (arg[0] = '-') OR (arg[0] = "/") DO
      strIx := 1;
      WHILE arg[strIx] <> nul DO
        ch := arg[strIx]; INC(strIx);
        IF (ch = "D") OR (ch = "n") THEN AbortMessage(loopMess,"") END;
        IF (ch = "c") OR (ch = "m") THEN clrTarget := TRUE END;
	IF ch = "S" THEN 
          persistent := TRUE;    (* Pass this to build *)
	ELSIF ch = "+" THEN 
          explain := TRUE;
	ELSIF ch = "?" THEN 
          UsageMessage();
        ELSE 
          myArgs[optIx] := ch; gpArgs[optIx] := ch; INC(optIx);
	END;
      END;
      INC(argNo);
      IF argNo < numOfArgs THEN
        GetArg(argNo,arg);
      ELSE 
        AbortMessage(usageStr,""); 
      END;
    END;
    options := optIx > 1;
    gpArgs[optIx] := "";		(* nul terminate *)
    IF explain THEN myArgs[optIx] := "+"; INC(optIx) END;
    myArgs[optIx] := "";		(* nul terminate *)
    IF persistent AND clrTarget THEN AbortMessage(clrMess,"") END;
  END GetGpmOptions;

  PROCEDURE CheckBldOptions(inArg  : ARRAY OF CHAR;
			  VAR outArg : ARRAY OF CHAR);

    TYPE  CharSet = SET OF CHAR;

    VAR ix, jx : CARDINAL;
        char   : CHAR;
  BEGIN
    ix := 0; jx := 0;
    REPEAT
      char := inArg[ix]; INC(ix); 
      IF char IN CharSet{"-", "g", "v", "V"} THEN
        outArg[jx] := char; INC(jx);
      END;
    UNTIL char = "";
    IF (jx > 0) AND (outArg[jx-1] = "-") THEN DEC(jx) END;
    options := jx <> 0;
    outArg[jx] := "";
  END CheckBldOptions;

  PROCEDURE Spawn(path : ARRAY OF CHAR; argv : ArgPtr) : INTEGER;
    VAR id     : INTEGER;
        result : Int32;

    PROCEDURE WriteArgs(argv : ArgPtr);
      TYPE S = POINTER TO ARRAY[0 .. 99] OF CHAR;
      TYPE P = POINTER TO ARRAY[0 .. 99] OF S;
      VAR p : P; i : INTEGER;
    BEGIN
      p := CAST(P,argv);
      i := 0;
      StdError.WriteString("Spawn: ");
      WHILE p^[i] <> NIL DO
        StdError.WriteString(p^[i]^); StdError.Write(" "); INC(i);
      END;
      StdError.WriteLn;
    END WriteArgs;

  BEGIN
   IF explain THEN WriteArgs(argv) END;
    result := Spawnv(path,argv);
    IF explain THEN
      StdError.WriteString("Spawn returned ");
      IF result < 0 THEN StdError.WriteString("negative");
      ELSE StdError.WriteCard(ORD(result),1);
      END;
      StdError.WriteLn;
    END;
    RETURN result;
  END Spawn;

BEGIN  (* main *)
  persistent := FALSE;
  explain    := FALSE;
  clrTarget  := FALSE;
  hasWswitch := FALSE;
  hasYswitch := FALSE;
  makName[0] := "";
  FormTmpNam();
  GetGpmOptions(options,argN,argStr,gpmStr);
  GetArg(argN,baseFileName);
  graphBuildArgs := Arg4(GRAPHBUILD,tFileName,argStr,baseFileName);
  result := Spawn(GRAPHBUILD,graphBuildArgs);
  IF result = 1 THEN
    ReadStringFromTempFile(errStr);
    AbortMessage(errStr,"");
  ELSIF result = 0 THEN
    ReadStringFromTempFile(makName);
    deciderArgs := Arg4(DECIDER,tFileName,argStr,makName);
(*
 *  deciderArgs := Arg3(DECIDER,tFileName,makName);
 *)
    result := Spawn(DECIDER,deciderArgs);
    WHILE result = 1 DO    (* need to compile a file *)
      ReadStringFromTempFile(fName);
      StdError.WriteString ("## compiling "); 
      StdError.WriteString (fName);
      StdError.WriteString (" ...");
      StdError.WriteLn;
      IF options THEN 
        gpmArgs := Arg3(GPM,gpmStr,fName);
      ELSE 
        gpmArgs := Arg2(GPM,fName);
      END;
      compRes := Spawn(GPM,gpmArgs);
      IF compRes >= 2 THEN
	AbortMessage(badRet,GPM);
      END;
      result := Spawn(DECIDER,deciderArgs);
    END;
    IF result = 2 THEN (* error detected *)
      ReadStringFromTempFile(errStr);
      AbortMessage(errStr,"");
    ELSIF result = 0 THEN
      IF clrTarget THEN
       (* skip *)
      ELSE
        ReadStringFromTempFile(fName);
        CheckBldOptions(gpmStr,gpmStr);   (* modifies options, gpmStr *)
        NewArgBlock(bldArgs,5);
        AppendArg(bldArgs,BUILD);
        IF options    THEN AppendArg(bldArgs,gpmStr) END;
        IF persistent THEN AppendArg(bldArgs,"-S") END;
        AppendArg(bldArgs,fName);
        StdError.WriteString ("## building "); 
        StdError.WriteString (fName);
        StdError.WriteString (" ...");
        StdError.WriteLn;
        result := Spawn(BUILD,ArgsOf(bldArgs));
        IF result <> 0 THEN AbortMessage(badRet,BUILD) END;
      END;
    ELSIF result # 3 THEN
      StdError.WriteString("Decider abort, result = ");
      StdError.WriteCard(result,0);
      StdError.WriteLn;
    END;
  ELSE
    AbortMessage(badRet,GRAPHBUILD);
  END;
  DeleteMakFile();
  IF result = 3 THEN
    StdError.WriteString("Target <");
    StdError.WriteString(baseFileName);
    StdError.WriteString("> is up to date");
    StdError.WriteLn;
  ELSIF (result = 0) AND explain THEN
    StdError.WriteString("Make completed successfully");
    StdError.WriteLn;
  END;
END GPMake.
