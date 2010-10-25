(*
 * =========== macro processed output from MPP  ==========
 *
 * input file  : gpm.mpp
 * time stamp  : 1997:01:12::08:29:14
 *
 * output file : gpm.mod
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
(*								*)
(*		Modula-2 Compiler Source Module			*)
(*								*)
(*		 Compiler Main Control Program.			*)
(*								*)
(*     (c) copyright 1989 Faculty of Information Technology.	*)
(*								*)
(*	original module : kjg August 1989. Code is based on	*)
(*			  the previous "c" language version	*)
(*	modifications   : jrh Oct 89 badArgs check              *)
(*			: kjg Feb 90 send -w to mips cc,	*)
(*				     and use a larger ArgBlock	*)
(*                        jrh Nov 90 Exec "/bin/cc", "cc -w ..."*)
(*			  kjg Jan 90 use GPMEDITOR variable ... *)
(*			  kjg Jan 90 always return 0 on success *)
(*			  kjg Feb 90 Apollo modificatons	*)
(*			  jrh Mar 92 Apollo cc errors, no any	*)
(*			  kjg Mar 92 cc result to gpmake	*)
(*                        pms Jul 93 GPMd for PC version        *)
(*                        pms Aug 93 Terminal instead of        *)
(*                                   StdError on PC             *)
(*                        pms Sep 93 Added modifications for pc *)
(*                                   cross compiler GP2TC       *)
(*								*)
(****************************************************************)

MODULE GPM;

 (*
  * This program starts off as a relatively small process, which
  * forks and then execs the compiler proper "gpm2". The parent
  * process waits for gpm2 to complete.
  *
  * gpm2 sends back a termination code which indicates the type
  * of termination, and hence the further action to be taken.
  *
  * gpm2 exit codes have the following meaning:
  *	0 ==> normal exit, ok to chain to cc
  *	1 ==> normal exit, no further action required
  *	2 ==> abnormal exit, gpm2 signalled errors
  *	3 ==> interactive exit, chain to vi
  *
  * In the case of interactive operation, when vi exits gpm2
  * is restarted with an explanatory message.
  *
  * The exit codes of this program are similar, and have
  * the following meanings to the shell:
  *      0 ==> normal exit, compilation succeeded
  *      0 ==> normal exit, no object code produced
  *      2 ==> abnormal, gpm2 signalled errors
  *      4 ==> abortion, gpm2 aborted with core dump
  *      5 ==> abnormal, gpm signalled bad arguments
  *
  * All messages from this program are directed to stderr.
  *
  * The temporary file is used by gpm2 to pass either:
  *   (1) the intermediate file name back to gpm, and thence to cc
  *   (2) an ex command back to gpm and thence to vi 
  * For example, if file xxxx.mod contains module AVeryLongName,
  * the temporary file will contain the name of the intermediate
  * file "averylon.c". The object filename will be "averylon.o".
  * Note the truncation and case transformation. This behaviour
  * can be overriden in the case of implementation modules so 
  * as to produce the output filenames "xxxx.c" and "xxxx.o"
  *)
(* ------------------------------------------------------------------ *)

  IMPORT Strings, WholeStr;
  FROM SYSTEM IMPORT ADR, CAST, ADDRESS;
  FROM Types  IMPORT Int32;
  FROM ProgArgs IMPORT 
        ArgNumber, GetArg, UNIXexit, Assert, EnvironString, VersionTime;
  FROM StdError IMPORT 
        WriteString, WriteCard, Write, WriteLn;
  FROM BuildArgs IMPORT 
        ArgPtr, ArgBlock, DisposeArgBlock, Arg3, Arg4,
	NewArgBlock, AppendArg, ArgsOf;
  FROM UxFiles IMPORT
	Open, Close, Delete, File, OpenMode, ReadNBytes;
  FROM Ascii IMPORT ht, lf;
  FROM UxProcesses IMPORT Fork, Execp, Wait, ProcessID;

(* ------------------------------------------------------------------ *)

  CONST edEnvStr = "GPMEDITOR";
	FrontEnd = "gpm2";
	gpm      = "gpm";
	GPM      = "GPM";

  CONST WS = WriteString; 
  CONST version = ".NET CLI for iap86";

  TYPE  MiddleString = ARRAY [0 .. 93] OF CHAR;
        NameString   = ARRAY [0 .. 15] OF CHAR;

  VAR   tmpNam : MiddleString;            (* name of tmp file  *)
        optStr : MiddleString; 		  (* option string     *)
        argStr : MiddleString;		  (* input file name   *)
        msg    : MiddleString;		  (* intermediate name *)
        edNam  : MiddleString;		  (* name of editor    *)
	objNam : MiddleString;		  (* object file name  *)
     
        persistent : BOOLEAN; (* ==> name.c file is not deleted  *)
	dPersists  : BOOLEAN; (* ==> -D switch *)
        profile    : BOOLEAN; (* ==> -p switch *)
        debug      : BOOLEAN; (* ==> -g switch *)
        explain    : BOOLEAN; (* ==> -X switch *)
	optimise   : BOOLEAN; (* ==> -O switch *)

        gpmArg : ArgPtr;   (* argument bundle for exec of gpm2 *)
        dgenBlk: ArgBlock; (* argument block for exec for dgen *)
        ccBlk  : ArgBlock; (* argument block for exec for cc   *)
        edBlk  : ArgBlock; (* argument block for exec of editor*)

        tmpFil : File;           (* the temporary, message file *)

        ok    : BOOLEAN;
	argN  : CARDINAL;	 (* number of arguments to gpm  *)
        argIx : CARDINAL; 	 (* index into the arg list     *)
        optIx : CARDINAL;	 (* index into the option str   *)
	defaultBuffSize : CARDINAL;
        result, retVal  : Int32;
	spitName : BOOLEAN;	 (* name is emitted to stdErr   *)
	dgenOFlg : CHAR;	 (* -O option for dgen          *)
	dgenNCnt : CARDINAL;	 (* -N option stuff for dgen    *)
	dgenNFlg : ARRAY [1 .. 20] OF CHAR;


  PROCEDURE DoUsageStr();
    VAR str : ARRAY [0..127] OF CHAR;
  BEGIN
    WS(GPM + " (" + version + ") version of "); VersionTime(str); WS(str);
    WS("Copyright 1996 Office of Commercial Services, " + 
       "Qld. University of Technology"+lf+lf);
    WS("Usage: " + gpm + " [options] filename(s)" + lf +
	"Options may be in any order, and in one or more groups" + lf +
	"Wildcards in filenames are permitted. " + gpm +
			" will warn if no files found" + lf);
 WS(" -a  turn off assertion checks        -d  dangerous: turn off warnings"+lf);
 WS(" -f  filename used as outname         -g  add debugging information"+lf);
 WS(" -I  interactive mode with editor     -i  turn off index checks"+lf);
 WS(" -l  listing name.lst is created      -n  no object code produced"+lf);
 WS(" -O0 turn off all optimisations       -Oc optimise for size"+lf);
 WS(" -Of optimise for speed               -r  turn off range checks"+lf);
 WS(" -S  'C' code output only             -s  turn off stack checks"+lf);
 WS(" -t  turn off overflow checks         -v  verbose compile messages"+lf);
 WS(" -V  super-verbose compile messages   -X  verbose error explanations"+lf);
    UNIXexit(1);
  END DoUsageStr;

  PROCEDURE Abort(str : ARRAY OF CHAR; cmd : ARRAY OF CHAR);
  BEGIN
    WriteString(gpm + ": ");
    WriteString(str); WriteString(cmd); WriteLn;
    UNIXexit(5);
  END Abort;

  PROCEDURE GetMessage(VAR str : ARRAY OF CHAR);
    VAR read : CARDINAL;
  BEGIN
    Open(tmpFil,tmpNam,ReadOnly,ok);
    IF ok THEN
      ReadNBytes(tmpFil,ADR(str),93,read);
      str[read] := "";
      Close(tmpFil,ok);
    ELSE Abort("Can't open ",tmpNam);
    END;
  END GetMessage;


  PROCEDURE GetEditorInfo(VAR nam : ARRAY OF CHAR;
			  VAR blk : ArgBlock);
    VAR rIdx, wIdx, mIdx : CARDINAL;
	wrkStr : MiddleString;			(* working string  *)
	msgStr : MiddleString;			(* mesg from gpm2  *)
        envStr : ARRAY [0 .. 255] OF CHAR;	(* environment str *) 

    PROCEDURE SkipSpace(VAR ix : CARDINAL);
    BEGIN
      WHILE (envStr[ix] = " ") OR (envStr[ix] = ht) DO INC(ix) END;
    END SkipSpace;

  BEGIN
    EnvironString(edEnvStr,envStr);
    GetMessage(msgStr);
    IF envStr[0] = "" THEN (* default editor is vi *)
      edNam := "vi";
      AppendArg(blk,edNam);
      AppendArg(blk,msgStr);
      AppendArg(blk,argStr);
    ELSE 
      Assert(msgStr[0] = "+");
      (*
       *  must parse envStr and construct the calling args
       *
       *    [space] edFilNam {arg | "%"}
       *
       *  within an arg "#" == line no
       *  "%" stands for the file_name
       *)
      rIdx := 0;
      wIdx := 0;
      SkipSpace(rIdx);
      WHILE envStr[rIdx] > " " DO
	edNam[wIdx] := envStr[rIdx]; INC(rIdx); INC(wIdx);
      END;
      edNam[wIdx] := "";
      AppendArg(edBlk,edNam);
      SkipSpace(rIdx);
      WHILE envStr[rIdx] <> "" DO (* split into args *)
       (*
	*   args are of two types -- "%" and others
	*)
	IF envStr[rIdx] = "%" THEN (* ==> filNam *)
	  AppendArg(edBlk,argStr); 
	  INC(rIdx); (* and go to next argument *)
	ELSE (* others *)
          wIdx := 0;
          WHILE envStr[rIdx] > " " DO  (* for every char in arg do... *)
  	    IF envStr[rIdx] <> "#" THEN (* copy char *)
	      wrkStr[wIdx] := envStr[rIdx]; 
	      INC(wIdx);
	    ELSE (* copy line *)
	      mIdx := 1;
	      WHILE msgStr[mIdx] <> "" DO
	        wrkStr[wIdx] := msgStr[mIdx]; 
		INC(wIdx); INC(mIdx);
	      END; (* cp *)
	    END; (* process one char *)
	    INC(rIdx); (* to next char *)
          END; (* while *)
          wrkStr[wIdx] := "";
	  AppendArg(edBlk,wrkStr);
          SkipSpace(rIdx);
        END; (* normal arg *)
      END; (* for each arg *)
    END; (* env is defined *)
  END GetEditorInfo;

  PROCEDURE FormTmpNam();
    VAR   index, pid : CARDINAL;
	   pidStr    : ARRAY [0 .. 15] OF CHAR;
    CONST prefix = "/tmp/"+gpm;
  BEGIN
    pid := ProcessID();
    tmpNam := prefix;
    WholeStr.IntToStr(pid,pidStr);
    Strings.Append(pidStr,tmpNam);
  END FormTmpNam;

  PROCEDURE Spawn(path : ARRAY OF CHAR; argv : ArgPtr) : CARDINAL;
    VAR id     : INTEGER;
        result : Int32;

    PROCEDURE WriteArgs(argv : ArgPtr);
      TYPE C = ARRAY [0 .. 99] OF CHAR;
      TYPE S = POINTER TO C;
      TYPE P = POINTER TO ARRAY [0 .. 99] OF S;
      VAR p : P; c : C; i, cx : [0 .. 99];
    BEGIN
      p := CAST(P,argv);
      i := 0;
      WriteString(gpm + ": ");
      WHILE p^[i] <> NIL DO
	cx := 0;
	REPEAT c[cx] := p^[i]^[cx]; INC(cx) UNTIL c[cx-1] = "";
        WriteString(c); Write(" "); INC(i);
      END;
      WriteLn;
    END WriteArgs;

  BEGIN
   IF explain THEN WriteArgs(argv) END;
   IF Fork() = 0 THEN (* in child *)
      Execp(path,argv);
      Abort("Couldn't exec ",path);
    ELSE (* in parent *)
      id := Wait(result);
      IF (result MOD 256) <> 0 THEN RETURN 5
      ELSE RETURN result DIV 256 END;
    END;
  END Spawn;

  PROCEDURE ScanOptStr(VAR oIx : CARDINAL);
    (* 
     *  scan a single option string for options
     *  which need to be passed to cc, and add
     *  the current arg string to the optStr
     *)
    VAR ix : CARDINAL; ch : CHAR;

    PROCEDURE GetNext();
    BEGIN
      optStr[oIx] := ch;
      INC(oIx); INC(ix);
      ch := argStr[ix];
    END GetNext;

  BEGIN
    (* assert: argStr[0] = "-" *)
    ix := 1; ch := argStr[1];
    WHILE ch <> "" DO
    (*
     * Note: No need to pick up -I switch
     *       Front ends will return 3 if they want us to load an editor
     * Note: No need to pick up -Cn switch, this is passed to gpmd anyhow.
     *)
      IF    ch = "S" THEN persistent  := TRUE;
      ELSIF ch = "D" THEN
        dPersists := TRUE; persistent := TRUE;	(* This is not build -D !! *)
	DEC(oIx); ch := optStr[oIx];		(* only for gpm...	   *)
      ELSIF ch = "p" THEN profile     := TRUE;	(* AppendArg(ccBlk,"-p"); *)
      ELSIF ch = "g" THEN debug       := TRUE;	(* AppendArg(ccBlk,"-g"); *)
      ELSIF ch = "X" THEN explain     := TRUE;
      ELSIF ch = "O" THEN			(* Turns on optimisations *)
	GetNext;
	dgenOFlg := ch;
	IF ch = "0" THEN
	  optimise := FALSE;
	  DEC(oIx,2); ch := optStr[oIx];	(* Throw away -O0 *)
	ELSE
	  optimise := TRUE;
	  IF    ch = "1" THEN
	    ch := "c";				(* -O1 = -Oc *)
	  ELSIF ch = "2" THEN
	    ch := "f";				(* -O2 = -Of *)
	  ELSIF (ch = "f") OR (ch = "t") THEN
	    dgenOFlg := "2";
	  ELSE
	    dgenOFlg := "1";			(* for dgen -Oc = -O1 *)
	  END;
	END;
      ELSIF ch = "N" THEN			(* Turns off optimisations *)
        DEC(oIx); ch := optStr[oIx];		(* just for dgen *)
	INC(ix); INC(dgenNCnt);
	dgenNFlg[dgenNCnt] := argStr[ix];
      ELSIF (ch = "W") OR (ch = "Y") THEN	(* for Build... ignore     *)
	DEC(oIx); ch := optStr[oIx];
      ELSIF ch = "B" THEN			(* default buffer size *)
	DEC(oIx); ch := optStr[oIx];
	defaultBuffSize := 0;
	WHILE (argStr[ix+1] >= "0") AND (argStr[ix+1] <= "9") DO
	  INC(ix);
	  defaultBuffSize := defaultBuffSize * 10 + ORD(argStr[ix]) - ORD("0");
        END;
      END;
      GetNext;
    END;
    optStr[oIx] := "";
  END ScanOptStr;

  VAR	ix, buffSize   : CARDINAL;
	dgenOpt        : ARRAY [0 ..  2] OF CHAR;
	tmpStr, sizStr : ARRAY [0 .. 15] OF CHAR;
BEGIN
  (*
   *  first some housekeeping chores
   *)
  FormTmpNam();       (* forms name "gpmNNNNN"  *)
  argN := ArgNumber();
  persistent  := FALSE;
  dPersists   := FALSE;
  debug       := FALSE;
  profile     := FALSE;
  explain     := FALSE;
  optimise    := FALSE;
  dgenOFlg    := "";
  dgenNCnt    := 0;
  defaultBuffSize := 5000;
  (*
   * building the arg list for gpm2
   * args are "gpm", [options,] tmpFileName, sourceFileName
   * in this case the fixed length arg pointer facilities are used
   *)
  argIx := 1;
  IF argN = 1 THEN DoUsageStr () END;
  (*
   *  first fetch all options -- these apply to all compilations
   *)
  optIx := 1; optStr := "-";
  GetArg(argIx,argStr);
  WHILE argStr[0] = '-' DO
    ScanOptStr(optIx);
    INC(argIx);
    IF argIx < argN THEN
      GetArg(argIx,argStr);
    ELSE DoUsageStr(); 
    END;
  END;
  (*
   *  now the main loop, which is executed for
   *  every separate remaining command line arg
   *)
  spitName := (argIx + 1) < argN;
  LOOP
    (*
     *  at this stage argStr is presumed to be a filename
     *)
    IF spitName THEN 
      WriteString(argStr); WriteLn;
    END;
    IF optIx = 1 THEN (* no options to pass *)
      gpmArg := Arg3(FrontEnd,tmpNam,argStr);
    ELSE 
      gpmArg := Arg4(FrontEnd,optStr,tmpNam,argStr);
    END;
    (*
     *  now the interactive loop is executed
     *  for each remaining argument in list
     *  this loop is normally traversed once only
     *  but may be traversed repeatedly for 
     *  compilations using the -I option
     *)
    LOOP  (* start compilation of a single file *)
      result := Spawn(FrontEnd,gpmArg);
      retVal := result;
      IF retVal <= 2 THEN EXIT;
      ELSIF retVal = 3 THEN (* chain to editor *)
       (*
        *  allocate an arg block for the editor
        *)
        NewArgBlock(edBlk,16);
        GetEditorInfo(edNam,edBlk);
	result := Spawn(edNam,ArgsOf(edBlk));
	DisposeArgBlock(edBlk);
        WriteString(lf + gpm + ": recompiling <");
        WriteString(argStr); Write(">"); WriteLn;
      ELSE EXIT;
      END; (* select on return value *)
    END; (* main loop *)

    IF result = 0 THEN
      GetMessage(msg);	(* fetches the intermediate file name *)
    END;
   (* 
    *  following actions depend on the returned value
    *  and the value of the persistent Booleans
    *)

    IF (result = 0) AND NOT persistent THEN (* chain to cc *)
     (*
      *  building the arg list for _cc_
      *  this uses a (variable length) ArgBlock
      *)
      NewArgBlock(ccBlk,16);  (* start arg block for cc *)
      AppendArg(ccBlk,"cc");
      AppendArg(ccBlk,"-c");
      AppendArg(ccBlk,"-w"); (* avoid warnings from coercions to ADDRESS *)
      IF profile  THEN AppendArg(ccBlk,"-p") END;
      IF debug    THEN AppendArg(ccBlk,"-g") END;
      IF optimise THEN AppendArg(ccBlk,"-O") END;
      AppendArg(ccBlk,msg);
      result := Spawn("cc",ArgsOf(ccBlk));
      DisposeArgBlock(ccBlk);
      IF result <> 0 THEN retVal := 4 END;   (* for gpmake *)
      Delete(msg,ok);	      (* deletes the name.c/s file *)
    END;
    Delete(tmpNam,ok);        (* deletes temporary file    *)
    INC(argIx);
    IF argIx = argN THEN EXIT ELSE GetArg(argIx,argStr) END;
  END; (* of per file loop *)
  IF retVal = 1 THEN retVal := 0 END; (* to keep Unix "make" happy *)
  UNIXexit(retVal);                   (* value for final file *)
END GPM.
