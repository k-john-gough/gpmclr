MODULE MBatchCLR;



(* MBatch is a program designed for running routine tests on the
   Gardens Point Modula 2 language system.
   The program parses a command file <filename.tst> and performs the
   compilation or build operations specified. A typical command file
   would consist of one or more test sequences. An example of a test 
   might be:
   
   * an asterisk denotes the start of a comment. 
   * to continue a comment over more than one line requires additional
   * asterisks.
   *
   # test 1 * test delimiter
   gpm -v program.def      * a compilation
   gpm program.mod         * another compilation
   ifok                    * continue if both compilations were successful     
                           * otherwise move onto next test.
   build program           * some comment
   ifok                    * run program if build was successful 
   run program
   <EOF>


   This program was written by Liam O'Rourke in September,1989.   *)

(*
 *  modifications       : tabs in input treated as space (kjg) 21-Nov-89
 *                      : marker in output for commands  (kjg) 21-Nov-89
 *                      : now recognizes "gpx" as comp   (kjg) 23-Nov-89
 *                      : now uses command line args     (kjg)  4-Jan-90
 *                      : do not dealloc arg-block!!!    (kjg) 10-Jul-90
 *                      : modified for CLR target        (kjg) 15-Dec-03
 *)


IMPORT SYSTEM;

FROM StdError IMPORT 
     Write, WriteString, WriteCard, WriteLn;
FROM Strings IMPORT
     Append, Replace, Assign, Length, Compare, CompareResults;
FROM ProgArgs IMPORT
     ArgNumber, GetArg, UNIXexit;
FROM BuildArgs IMPORT
     ArgPtr, ArgBlock, NewArgBlock, DisposeArgBlock, AppendArg, ArgsOf;
FROM UxFiles IMPORT
     Open, Close, File, OpenMode, ReadByte, Delete;
FROM Ascii IMPORT
     ht, lf, cr;
FROM Types IMPORT
     Int32;
FROM PcProcesses IMPORT System, Spawnv;

CONST  EOL=lf;
       CRT=cr;
       EOF=377C;
       CommentCh="*"; (* comment delimiter in command file *)
       MaxArgs=6;     (* a line in the input file may contain no more than *)
                      (* MaxArgs words (excluding comments) *)

TYPE  String = ARRAY [0 .. 255] OF CHAR;
      StringPosition = CARDINAL[0..80]; (* Index type for input lines *)

CONST   errPrefix  = "  ?? ";
        comPrefix  = "  -- ";
        echoPrefix = "  => ";

VAR  
     done : BOOLEAN;
     file : File;
     name : String;
     result : Int32;     (* exit code returned to this process by children *)
     line : String;      (* a line from the input file *)
     firstWord : String; (* the first non-blank contiguous string in line *)
     moduleName : String;(* the name of a test module, used in calls to the *)
                         (* file deletion procedure *)
     globPos : StringPosition; (* character position index to line *)
     args : ArgPtr;      (* points to command line arguments *)
     ok,                 (* set to true at the start of a test sequence, set
                            false if a compilation or build attempt fails *)
     seekNextTest : BOOLEAN; (* set to true if the test contains the line
                                "ifok" and the Boolean "ok" is false. *)



PROCEDURE GetNextLine (VAR line : String);

(* Reads a line from stdin, returns this in the string line. *)
(* Appends nullchar to line. *)

VAR  linePos : StringPosition;
     ch : CHAR;

BEGIN   (* GetNextLine *)
  linePos := 0;
  REPEAT ReadByte(file,ch) UNTIL (ch <> EOL) AND (ch <> CRT);
  WHILE (ch <> EOL) AND (ch <> CRT) AND (ch <> EOF) DO
    line[linePos] := ch;
    INC(linePos);
    ReadByte(file,ch);
  END;
  line[linePos]:="";
  done := ch <> EOF;
END GetNextLine;


PROCEDURE NextWord (line : String;
                    VAR linePos : StringPosition;
                    VAR nextWord : String);       

(* Returns next word in a line, skipping leading spaces.*)
(* Post-condition : linePos points to the position in line *)
(* one past the end of word. *)

CONST  SPACE = " ";

VAR ch : CHAR;
    wordPos : StringPosition;
    endOfWord : BOOLEAN;

BEGIN  (* NextWord *)
  ch := line[linePos];
  WHILE (ch = SPACE) OR (ch = ht) DO    (* skip spaces *)
    INC(linePos);
    ch := line[linePos];
  END;
  (* get next word *)
  wordPos := 0;
  IF (ch=EOL) OR (ch=CRT) OR (ch="") OR (ch=CommentCh) THEN
    nextWord[0]:=00C; (* append null *)
    INC(linePos);  (* for post-condition *)
  ELSE
    endOfWord:=FALSE;
    WHILE NOT endOfWord DO
      nextWord[wordPos] := ch;
      INC(wordPos);
      INC(linePos);
      ch := line[linePos];
      endOfWord := (ch=SPACE) OR (ch=ht) OR (ch=EOL) OR (ch=CRT) OR (ch="");
    END;  (* while *)
    nextWord[wordPos] := 00C (* append null *)
  END;  (* if then else *)
END NextWord;


PROCEDURE GetArgs (line : String; prefix : ARRAY OF CHAR):ArgPtr;

(* GetArgs returns a pointer to the arguments in a command line *)
(* It ignores all characters after the comment symbol "*"       *)

VAR linePos : StringPosition;
    nextArg : String;
    argBlk  : ArgBlock;
    args    : ArgPtr;
    ended   : BOOLEAN;

BEGIN  (* GetArgs *)
  ended   := FALSE;
  linePos := 0;
  NewArgBlock(argBlk,MaxArgs);

  NextWord(line,linePos,nextArg); 
  AppendArg(argBlk,nextArg);
  IF prefix[0] # "" THEN AppendArg(argBlk,prefix) END;

  NextWord(line,linePos,nextArg); ended := (nextArg[0] = "");
  WHILE NOT ended DO
    AppendArg(argBlk,nextArg);
    NextWord(line,linePos,nextArg); ended := (nextArg[0] = "");
  END;
  args := ArgsOf(argBlk);
(*
 *   DisposeArgBlock(argBlk);
 *)
  RETURN (args);
END GetArgs;


PROCEDURE Run (command : String;
               args : ArgPtr;
               VAR result : Int32);


(* executes command with arguments args. If command does not exec  *)
(* or if command aborts, result := 5 *)

VAR rc : INTEGER;

    PROCEDURE WriteArgs(argv : ArgPtr);
      TYPE C = ARRAY [0 .. 99] OF CHAR;
      TYPE S = POINTER TO C;
      TYPE P = POINTER TO ARRAY [0 .. 99] OF S;
      VAR p : P; c : C; i, cx : [0 .. 99];
    BEGIN
      p := SYSTEM.CAST(P,argv);
      i := 0;
      WriteString("args: ");
      WHILE p^[i] <> NIL DO
        cx := 0;
        REPEAT c[cx] := p^[i]^[cx]; INC(cx) UNTIL c[cx-1] = "";
        WriteString(c); Write(" "); INC(i);
      END;
      WriteLn;
    END WriteArgs;

BEGIN  (* Run *)
(*
 *  WriteArgs(command, args);
 *)
  rc := Spawnv(command, args);
  IF rc = -1 THEN
    result := 5;
    WriteString(errPrefix);
    WriteString(command);
    WriteString(": cannot exec or aborted");
    WriteLn;
(*
 *  UNIXexit(result);
 *)
  ELSE
    result := rc;
  END;
END Run;

PROCEDURE DelFiles(fileName : String);

(* Deletes all files wich may have been produced by GPM or Build *)
(* with names of the form "fileName", or "fileName.tag" *)
(* In many instances, this procedure will attempt to delete files *)
(* which do not exist *)

VAR actualName:String;
    nameLength:CARDINAL;
    ok : BOOLEAN;  (* dummy parameter for call to library delete,
                      the result is never tested. *)

BEGIN
  nameLength := Length(fileName);
  Assign(fileName,actualName);
  Delete(actualName,ok);
  Append(".dll",actualName);
  Delete(actualName,ok);
  Assign(fileName,actualName);
  Append(".exe",actualName);
  Delete(actualName,ok);
  Replace(".syx",nameLength,actualName);
  Delete(actualName,ok);
  Replace(".il",nameLength,actualName);
  Delete(actualName,ok);
  Replace(".lst",nameLength,actualName);
  Delete(actualName,ok);
(*
 *  Delete("core",ok);
 *)
END DelFiles;



BEGIN  (* MBatch *)
  IF ArgNumber() <> 1 THEN
    WriteString(errPrefix);
    WriteString("MBatch usage: mbatch file.tst"); WriteLn;
    WriteString(errPrefix);
    WriteString("program MBatch terminating."); WriteLn;
    UNIXexit(0);
  ELSE
    GetArg(0,name);
    Open(file,name,ReadOnly,done);
    IF NOT done THEN
      WriteString(errPrefix);
      WriteString("Input file cannot be opened."); WriteLn;
      WriteString(errPrefix);
      WriteString("program MBatch terminating."); WriteLn;
      UNIXexit(0);
    END;
  END;

  GetNextLine(line);
  globPos := 0;
  ok := TRUE;
  seekNextTest := FALSE;
  NextWord(line,globPos,firstWord);

  WHILE done DO   (* perform each test in file *)
    IF firstWord[0] = "#" THEN   (* start of next test *)
      ok := TRUE;
      seekNextTest := FALSE;
      WriteLn; 
      WriteString(echoPrefix);
      WriteString(line);
      WriteLn;
    ELSE
      IF NOT seekNextTest THEN
        WriteString(echoPrefix);
        WriteString(line);  (* echo input *)
        WriteLn;
        IF (Compare(firstWord, "gpm")=equal) OR
           (Compare(firstWord, "gpx")=equal) THEN  (* compile *)
          firstWord := "gpx";
          args := GetArgs(line, "-c");
          Run(firstWord,args,result);
          IF result > 1 THEN  (* compilation unsuccessful *)
            ok := FALSE;
          END 
        ELSIF Compare(firstWord,"build")=equal THEN  (* build *)
          args := GetArgs(line, "");
(*
 *  No "build" for the CLR ...
 *
 *        Run("build",args,result);
 *        IF result <> 0 THEN (* build unsuccessful *)
 *          ok := FALSE;
 *        END  
 *)
        ELSIF Compare(firstWord,"ifok")=equal THEN  
          IF NOT ok THEN
            WriteLn; 
            WriteString(comPrefix);
            WriteString("jumping to next #"); WriteLn;
            seekNextTest := TRUE; 
          END
        ELSIF Compare(firstWord,"delete")=equal THEN 
          (* remove files associated with this test *)
          (* .mod and .def files remain! *)
          NextWord(line,globPos,moduleName);
          DelFiles(moduleName) 
        ELSIF (firstWord[0] <> CommentCh) AND 
              (firstWord[0] <> "") THEN (* assume executable *)
          args := GetArgs(line, "");
          WriteLn;
(*
 *          result := System(line);
 *)
          Run(firstWord,args,result);  
          WriteLn;
          WriteString(comPrefix);
          WriteString("result code:  ");  
          WriteCard(ABS(result),3);
          WriteLn;
          IF result = 5 THEN ok := FALSE END;
        END;  (* IF-ELSIF *)
      END;  (* IF NOT seekNextTest *)
    END;  (* IF-ELSE *)

    GetNextLine(line);
    globPos := 0;
    NextWord(line,globPos,firstWord);

  END;   (* while not end of file *)
  WriteLn;
  Close(file,done);
END MBatchCLR.
