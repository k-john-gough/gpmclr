
(****************************************************************)
(*                                                              *)
(*              Modula-2 Compiler Source Module                 *)
(*                                                              *)
(*               Compiler Main Control Program.                 *)
(*                                                              *)
(*     (c) copyright 1989 Faculty of Information Technology.    *)
(*                                                              *)
(*        original module : kjg August 1989. Code is based on   *)
(*                          the previous "c" language version   *)
(*        modifications   : jrh Oct 89 badArgs check            *)
(*                        : kjg Feb 90 send -w to mips cc,      *)
(*                             and use a larger ArgBlock        *)
(*                        jrh Nov 90 Exec "/bin/cc", "cc -w ..."*)
(*                        kjg Jan 90 use GPMEDITOR variable ... *)
(*                        kjg Jan 90 always return 0 on success *)
(*                        kjg Feb 90 Apollo modificatons        *)
(*                        jrh Mar 92 Apollo cc errors, no any   *)
(*                        kjg Mar 92 cc result to gpmake        *)
(*                        pms Jul 93 GPMd for PC version        *)
(*                        pms Aug 93 Terminal instead of        *)
(*                                   StdError on PC             *)
(*                        pms Sep 93 Added modifications for pc *)
(*                                   cross compiler GP2TC       *)
(*                                                              *)
(****************************************************************)

MODULE GPX;

 (*
  * This program starts off as a relatively small process, which
  * forks and then execs the compiler proper "gpmx". The parent
  * process waits for gpmx to complete.
  *
  * gpmx sends back a termination code which indicates the type
  * of termination, and hence the further action to be taken.
  *
  * gpmx exit codes have the following meaning:
  *        0 ==> normal exit, ok to chain to cc (or ILASM)
  *        1 ==> normal exit, ok to chain to ILASM with /DLL flag
  *        2 ==> normal exit, no further action required
  *        3 ==> interactive exit, chain to vi
  *        4 ==> abnormal exit, gpm2 signalled errors
  *
  * In the case of interactive operation, when vi exits gpmx
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
  * The temporary file is used by gpmx to pass either:
  *   (1) the intermediate file name back to gpd, and thence to 
  *       ilasm or (dgen ; as) as the case may be.
  *   (2) an ex command back to gpm and thence to vi 
  * For example, if file xxxx.mod contains module AVeryLongName,
  * the temporary file will contain the name of the intermediate
  * file "averylon.il". The object filename will be "averylon.dll".
  * Note the truncation and case transformation. This behaviour
  * can be overriden in the case of implementation modules so 
  * as to produce the output filenames "xxxx.il" and "xxxx.dll"
  * ------------------------------------------------------------------ *)

IMPORT StdError;

  IMPORT Strings, WholeStr, Wildcards;
  FROM SYSTEM IMPORT ADR, CAST, ADDRESS;
  FROM Types  IMPORT Int32;
  FROM ProgArgs IMPORT 
        ArgNumber, GetArg, UNIXexit, UNIXtime,
        Assert, EnvironString, VersionTime;
  FROM StdError IMPORT 
        WriteString, WriteCard, Write, WriteLn;
  FROM BuildArgs IMPORT 
        ArgPtr, ArgBlock, DisposeArgBlock, Arg3, Arg4,
        NewArgBlock, AppendArg, ArgsOf;
  FROM UxFiles IMPORT
        Open, Close, Delete, File, OpenMode, ReadNBytes;
  FROM Ascii IMPORT ht, lf;
  FROM PcProcesses IMPORT Spawnv, PSP;

(* ------------------------------------------------------------------ *)

  CONST edEnvStr = "GPMEDITOR";
        FrontEnd = "gpmx";
        gpm      = "gpx";
        GPM      = "Gardens Point Modula-2";

  CONST WS = WriteString; 
  CONST version = "GPM-CLR";

  TYPE  MiddleString = ARRAY [0 .. 93] OF CHAR;
        NameString   = ARRAY [0 .. 15] OF CHAR;

  VAR   tmpNam : MiddleString;            (* name of tmp file  *)
        optStr : MiddleString;            (* option string     *)
        argStr : MiddleString;            (* input file name   *)
        msg    : MiddleString;            (* intermediate name *)
        edNam  : MiddleString;            (* name of editor    *)
        objNam : MiddleString;            (* object file name  *)
     
        persistent : BOOLEAN; (* ==> name.s file is not deleted  *)
        dPersists  : BOOLEAN; (* ==> -D switch *)
        profile    : BOOLEAN; (* ==> -p switch *)
        debug      : BOOLEAN; (* ==> -g switch *)
        explain    : BOOLEAN; (* ==> -X switch *)
        optimise   : BOOLEAN; (* ==> -O switch *)
        verbose    : BOOLEAN;
        clrTarget  : BOOLEAN;
        doHelp     : BOOLEAN;

        gpmArg : ArgPtr;   (* argument bundle for exec of gpm2 *)
        dgenBlk: ArgBlock; (* argument block for exec for dgen *)
        ccBlk  : ArgBlock; (* argument block for exec for cc   *)
        edBlk  : ArgBlock; (* argument block for exec of editor*)

        tmpFil : File;          (* the temporary, message file *)

        ok    : BOOLEAN;
        argN  : CARDINAL;       (* number of arguments to gpm  *)
        argIx : CARDINAL;       (* index into the arg list     *)
        optIx : CARDINAL;       (* index into the option str   *)
        defaultBuffSize : CARDINAL;
        result, retVal  : Int32;
        spitName : BOOLEAN;     (* name is emitted to stdErr   *)
        dgenOFlg : CHAR;        (* -O option for dgen          *)
        dgenNCnt : CARDINAL;    (* -N option stuff for dgen    *)
        dgenNFlg : ARRAY [1 .. 20] OF CHAR;


  PROCEDURE DoUsageStr(n : CARDINAL);
    VAR str : ARRAY [0..127] OF CHAR;
  BEGIN
    WS(GPM + " (" + version + ") version of "); VersionTime(str); WS(str);
    WS("Copyright 1996-2004 Queensland University of Technology (QUT)"+lf);
    WS("Faculty of Information Technology, Gardens Point, Brisbane, AUSTRALIA"+
        lf+lf);
    WS("Usage: " + gpm + " [options] filename(s)" + lf +
        "Options may be in any order, and in one or more groups" + lf +
        "Wildcards in filenames are permitted. " + gpm +
                        " will warn if no files found" + lf);
    WS("Unix style options with prefix '-' are also accepted"+lf);
 WS(" /a  turn off assertion checks        /Bn allocate 'n' buffer entries"+lf);
 WS(" /c  .NET CIL produced (same as -m)"+lf);
 WS(" /Cn, where n~['0'..'8']: rewrite CASE tables to keep density > n/8"+lf);
 WS(" /D  D-Code output only               /d  dangerous: turn off warnings"+lf);
 WS(" /f  filename used as outname         /g  add debugging information"+lf);
 WS(" /I  interactive mode with editor     /i  turn off index checks"+lf);
 WS(" /m  .NET CIL produced (same as -c)"+lf);
 WS(" /l  listing name.lst is created      /n  no object code produced"+lf);
 WS(" /N[cflpr] turn off dgen optimisation /O0 turn off all optimisations"+lf);
 WS(" /O1 default optimisations (= -Oc)    /O2 turn on all optimisations"+lf);
 WS(" /Of optimise for speed               /r  turn off range checks"+lf);
 WS(" /S  assembler output only            /s  turn off stack checks"+lf);
 WS(" /t  turn off overflow checks         /v  verbose compile messages"+lf);
 WS(" /V  super-verbose compile messages   /x+ language extensions turned on"+lf);
 WS(" /x- language extensions turned off   /X  verbose error explanations"+lf);
 WS(" /?  output this usage message"+lf);
    IF n <> 0 THEN UNIXexit(1) END;
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

  PROCEDURE ChangeExt(VAR name : ARRAY OF CHAR; ext : ARRAY OF CHAR);
    VAR ix,t : CARDINAL;
  BEGIN
    ix := LENGTH(name);
    WHILE ((ix > 0) AND (name[ix] <> ".")) DO DEC(ix) END;
    IF name[ix] <> "." THEN ix := LENGTH(name) END;
    name[ix] := ".";
    INC(ix);
    FOR t := 0 TO HIGH(ext) DO
      name[ix+t] := ext[t];
      IF ext[t] = "" THEN RETURN END;
    END;
  END ChangeExt;

  PROCEDURE GetEditorInfo(VAR nam : ARRAY OF CHAR;
                          VAR blk : ArgBlock);
    VAR rIdx, wIdx, mIdx : CARDINAL;
        wrkStr : MiddleString;                    (* working string  *)
        msgStr : MiddleString;                    (* mesg from gpm2  *)
        envStr : ARRAY [0 .. 255] OF CHAR;        (* environment str *) 

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
    CONST prefix = "\tmp\"+gpm;
  BEGIN
    pid := UNIXtime();
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
    result := Spawnv(path, argv);
    IF explain THEN
      WriteString("spawn returned ");
      IF result < 0 THEN WriteString("negative");
      ELSE WriteCard(ORD(result),1);
      END;
      WriteLn;
    END;
    IF result < 0 THEN result := 5 END;
    RETURN result;
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
    (* assert: argStr[0] = "-" OR "/" *)
    ix := 1; ch := argStr[1];
    WHILE ch <> "" DO
    (*
     * Note: No need to pick up -I switch
     *       Front ends will return 3 if they want us to load an editor
     * Note: No need to pick up -Cn switch, this is passed to gpmd anyhow.
     *)
      IF    ch = "?" THEN doHelp      := TRUE;
      ELSIF ch = "S" THEN persistent  := TRUE;
      ELSIF ch = "D" THEN
        dPersists := TRUE; persistent := TRUE;    (* This is not build -D !! *)
        DEC(oIx); ch := optStr[oIx];              (* only for gpm...         *)
      ELSIF ch = "p" THEN profile     := TRUE;    (* AppendArg(ccBlk,"-p");  *)
      ELSIF (ch = "c") OR (ch = "m") THEN 
(*
 *      persistent := TRUE;            (* temporary FIX ME LATER *)
 *)
        clrTarget  := TRUE;
      ELSIF ch = "g" THEN debug       := TRUE;    (* AppendArg(ccBlk,"-g");  *)
      ELSIF ch = "X" THEN explain     := TRUE;
      ELSIF ch = "v" THEN verbose     := TRUE;
      ELSIF ch = "V" THEN verbose     := TRUE;
      ELSIF ch = "O" THEN                         (* Turns on optimisations  *)
        GetNext;
        dgenOFlg := ch;
        IF ch = "0" THEN
          optimise := FALSE;
          DEC(oIx,2); ch := optStr[oIx];           (* Throw away -O0 *)
        ELSE
          optimise := TRUE;
          IF    ch = "1" THEN
            ch := "c";                             (* -O1 = -Oc *)
          ELSIF ch = "2" THEN
            ch := "f";                             (* -O2 = -Of *)
          ELSIF (ch = "f") OR (ch = "t") THEN
            dgenOFlg := "2";
          ELSE
            dgenOFlg := "1";                       (* for dgen -Oc = -O1 *)
          END;
        END;
      ELSIF ch = "N" THEN                        (* Turns off optimisations *)
        DEC(oIx); ch := optStr[oIx];             (* just for dgen *)
        INC(ix); INC(dgenNCnt);
        dgenNFlg[dgenNCnt] := argStr[ix];
      ELSIF (ch = "W") OR (ch = "Y") THEN        (* for Build... ignore     *)
        DEC(oIx); ch := optStr[oIx];
      ELSIF ch = "B" THEN                        (* default buffer size *)
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

  (* ------------------------------ *)
  MODULE FileNameIterator;
(*
IMPORT StdError;
 *)
    IMPORT MiddleString, GetArg, GetArg, hasWildcards, CAST, Wildcards;
    EXPORT InitIterator, GetNextArg, hasWildcards;

    TYPE ChArrayPtr = POINTER TO ARRAY [0 .. 7] OF CHAR;
    TYPE UxArgBlock = POINTER TO ARRAY [0 .. 7] OF ChArrayPtr;

    VAR  argNum : CARDINAL;
         argLim : CARDINAL;
         argTmp : MiddleString;
         argPtr : UxArgBlock;
         argIdx : CARDINAL;

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

    PROCEDURE InitIterator(idx, lim : CARDINAL);
    BEGIN
      argNum := idx;
      argLim := lim;
      argPtr := NIL;
    END InitIterator;

(* $I- Turn off index bounds checks *)
(* $R- Turn off range bounds checks *)

    PROCEDURE GetNextArg(VAR arg : ARRAY OF CHAR; VAR ok : BOOLEAN);
      (* ---- *)
      PROCEDURE AssignT(VAR s : ARRAY OF CHAR);
        VAR i : CARDINAL;
      BEGIN
        FOR i := 0 TO HIGH(s) DO s[i] := argTmp[i] END;
      END AssignT;
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
      IF argPtr # NIL THEN
        strPtr := argPtr^[argIdx]; INC(argIdx);
       (*
        *  We are inside a wildcard iteration.
        *  Check if there are arguments left.
        *)
        IF strPtr # NIL THEN
         (*
          *  Yes there are args left.  Return the next one.
          *)
          AssignP(arg, strPtr); ok := TRUE; RETURN; (* PRE-EMPTIVE EXIT *)
        ELSE
         (*
          *  No args left, fall through to next code
          *)
          argPtr := NIL;
          argIdx := 0;
        END;
      END;
     (*
      *  Next: check if we there are command line args left.
      *)
      IF argNum = argLim THEN ok := FALSE; RETURN END; (* PRE-EMPTIVE EXIT *)
     (*
      *  If so, then get the next one ...
      *)
      GetArg(argNum, argTmp); INC(argNum);
     (*
      *  Check: does the next argument have wildcards
      *)
      IF hasWildcards(argTmp) THEN
        (*
         *  If so, then initialize another iteration and recurse.
         *)
         argPtr := CAST(UxArgBlock, 
                        Wildcards.GetMatchingFiles(".", argTmp));
         GetNextArg(arg, ok);
      ELSE
        (*
         *  If not, then pass the command line arg back unchanged.
         *)
        AssignT(arg); ok := TRUE;
      END;
    END GetNextArg;

(* $I= *)
(* $R= *)
  BEGIN
    argPtr := NIL;
  END FileNameIterator;
  (* ------------------------------ *)

  VAR   ix, buffSize   : CARDINAL;
        valid          : BOOLEAN;
        dgenOpt        : ARRAY [0 ..  2] OF CHAR;
        tmpStr, sizStr : ARRAY [0 .. 15] OF CHAR;

BEGIN
 (*
  *  First some housekeeping chores
  *)
  FormTmpNam();       (* forms name "gpmNNNNN"  *)
  argN := ArgNumber();
  persistent  := FALSE;
  dPersists   := FALSE;
  debug       := FALSE;
  profile     := FALSE;
  explain     := FALSE;
  optimise    := FALSE;
  clrTarget   := FALSE;
  doHelp      := FALSE;
  dgenOFlg    := "";
  dgenNCnt    := 0;
  defaultBuffSize := 5000;
 (*
  * building the arg list for gpmx
  *
  * When called from the UNIX command line, the zero arg is the
  * program name. Args are gpx [options,] tmpFileName, sourceFileName
  * In this case the fixed length arg pointer facilities are used
  *
  * When called from the DOS command line, the zero arg is not
  * the program name, thus args are [options,] tmpFileName, sourceFileName
  * In this case the fixed length arg pointer facilities are used
  *)
  argIx := 0;
  IF argN = argIx THEN DoUsageStr(1) END;
  (*
   *  first fetch all options -- these apply to all compilations
   *)
  optIx := 1; optStr := "-";
  GetArg(argIx,argStr);
  WHILE (argStr[0] = '/') OR (argStr[0] = '-') DO
    ScanOptStr(optIx);
    INC(argIx);
    IF argIx < argN THEN
      GetArg(argIx,argStr);
    ELSE DoUsageStr(1);             (* this call does not return *)
    END;
  END;
  IF doHelp THEN DoUsageStr(0) END;
 (*
  *  now the main loop, which is executed for
  *  every separate remaining command line arg
  *)
  spitName := ((argIx + 1) < argN) OR hasWildcards(argStr);
  InitIterator(argIx, argN);
  LOOP
    GetNextArg(argStr, valid); IF NOT valid THEN EXIT END;
    (*
     *  at this stage argStr is presumed to be a filename
     *)
    IF spitName THEN 
      WriteString(argStr); WriteLn;
    END;
    IF optIx = 1 THEN (* no options to pass *)
      gpmArg := Arg3(FrontEnd, tmpNam, argStr);
    ELSE 
      gpmArg := Arg4(FrontEnd, optStr, tmpNam, argStr);
    END;
   (*
    *  now the interactive loop is executed
    *  for each remaining argument in list
    *  this loop is normally traversed once only
    *  but may be traversed repeatedly for 
    *  compilations using the -I option
    *)
    LOOP  (* start compilation of a single file *)
      result := Spawn(FrontEnd, gpmArg);
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

    IF result <= 1 THEN
      GetMessage(msg);        (* fetches the intermediate file name *)
    END;
   (* 
    *  Optionally call the D-Code back end.
    *  following actions depend on the returned value
    *  and the value of the persistent Booleans
    *)
    IF (result = 0) AND NOT clrTarget AND NOT dPersists THEN (* chain to dgen *)
     (*
      *  building the arg list for dgen
      *  this uses a (variable length) ArgBlock
      *)
      buffSize := defaultBuffSize;
      LOOP
        NewArgBlock(dgenBlk,16);
        AppendArg(dgenBlk,"dgen");
        IF debug   THEN AppendArg(dgenBlk,"-g") END;
        IF explain THEN AppendArg(dgenBlk,"-X") END;
        IF profile THEN AppendArg(dgenBlk,"-p") END;
        IF dgenOFlg <> "" THEN 
          dgenOpt := "-O"; dgenOpt[2] := dgenOFlg;
          AppendArg(dgenBlk,dgenOpt);
        END;
        FOR ix := 1 TO dgenNCnt DO
          dgenOpt := "-N"; dgenOpt[2] := dgenNFlg[ix];
          AppendArg(dgenBlk,dgenOpt);
        END;
        WholeStr.IntToStr(buffSize,sizStr);
        tmpStr := "-B";
        Strings.Append(sizStr,tmpStr);
        AppendArg(dgenBlk,tmpStr);
        AppendArg(dgenBlk,msg);
        result := Spawn("dgen",ArgsOf(dgenBlk));
        DisposeArgBlock(dgenBlk);
        IF result <> 0 THEN
          IF result = 3 THEN        (* Try again with double the buffer size *)
            buffSize := buffSize * 2;
            WriteString("Retrying with -B"); WriteCard(buffSize,0); WriteLn;
          ELSE
            WriteString("** dgen failed, result # ");
            WriteCard(result,3); WriteLn;
            retVal := 4;
            EXIT;
          END;
        ELSE EXIT;
        END;
      END;
      Delete(msg,ok);                (* deletes the name.dcf file  *)
      objNam := msg; ChangeExt(objNam,"o");
      ChangeExt(msg,"s");                      (* changes name.dcf to name.s *)
    END;
   (*
    *  Optionally call the assembler.
    *  Either the native code assembler or ILASM, as appropriate.
    *)
    IF NOT persistent AND (result <= 1) THEN (* Call assembler *)
     (*
      *  building the arg list for the assembler
      *  this uses a (variable length) ArgBlock
      *)
      NewArgBlock(ccBlk,16);  (* start arg block for assembler *)
      IF clrTarget THEN
        AppendArg(ccBlk,"ilasm");
        IF debug THEN AppendArg(ccBlk,"/debug") END;
        IF NOT verbose THEN AppendArg(ccBlk, "/quiet") END;
        IF result = 1  THEN
          AppendArg(ccBlk, "/DLL");
        ELSE
          AppendArg(ccBlk, "/EXE");
        END;
        AppendArg(ccBlk, msg);   (* Input .il filename  *)
        result := Spawn("ilasm", ArgsOf(ccBlk));
      ELSE
        IF debug THEN
          AppendArg(ccBlk,"gcc");
          AppendArg(ccBlk,"-g");
          AppendArg(ccBlk,"-c");
          AppendArg(ccBlk,msg);    (* Input .s filename  *)
          result := Spawn("gcc",ArgsOf(ccBlk));
        ELSE
          AppendArg(ccBlk,"as");
          AppendArg(ccBlk,"-o");
          AppendArg(ccBlk,objNam); (* Output .o filename *)
          AppendArg(ccBlk,msg);    (* Input .s filename  *)
          result := Spawn("as",ArgsOf(ccBlk));
        END;
      END;
      DisposeArgBlock(ccBlk);
      IF result <> 0 THEN retVal := 4 END;   (* for gpmake *)
      Delete(msg,ok);              (* deletes the name.c/s file *)
    END;
    Delete(tmpNam,ok);        (* deletes temporary file    *)
  END; (* of per file loop *)
  IF retVal <= 2 THEN retVal := 0 END; (* to keep Unix "make" happy *)
  UNIXexit(retVal);                   (* value for final file *)
END GPX.
