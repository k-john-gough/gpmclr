(*
 * =========== macro processed output from MPP  ==========
 *
 * input file  : grepdef.mpp
 * time stamp  : 1996:11:07::05:13:32
 *
 * output file : grepdef.mod
 * created at  : 2004:01:12::14:21:43
 *
 * options ... :  /Ddotnet86
 *
 * =======================================================
 *)

(* -- RCS Header --
		$Log:	grepdef.mpp,v $
Revision 1.1  94/01/12  15:37:06  mboss
Initial revision

*)

(* 
 *  extracted with 
 * 	    "opsys" == "windows"
 * 	   "endian" == "little"
 *	"processor" == "iap386"
 *)

(* ================================================================ *)
(* Preliminary utility module for Gardens Point Modula              *)
(*                                                                  *)
(*                           GREPDEF.MOD                            *)
(*                                                                  *)
(*  Original Module :                                               *)
(*  Modifications   :                                               *)
(*  24-May-92  jrh  Use standard string sizes from gpmake (mkinout) *)
(*  16-Dec-93  pms  Added Windows NT changes                        *)
(* ================================================================ *)

MODULE GrepDef;


  IMPORT Ascii, StdError;
  FROM UxFiles IMPORT File, ReadByte, EndFile;
  FROM InOut IMPORT WriteString, Write, WriteLn;
  FROM ProgArgs IMPORT ArgNumber, GetArg, EnvironString;
  FROM Strings  IMPORT Append, Compare, CompareResults;
  FROM ShellPipes IMPORT PipeInput, ClosePipe;

FROM BuildArgs IMPORT ArgPtr;

  CONST
    middleMax = 255;	(* Upper bound of middle-size strings -
			   $M2SYM & single path names *)
    shortMax = 80;	(* Upper bound of short strings - 
			   args, error messages *)
    fileNameMax = 80;	(* Upper bound of file names - 
			   identifier + extension *)

  TYPE
    MiddleIndex    = [0 .. middleMax];
    ShortIndex     = [0 .. shortMax];
    FileNameIndex  = [0 .. fileNameMax];
    MiddleString   = ARRAY MiddleIndex   OF CHAR;
    ShortString    = ARRAY ShortIndex    OF CHAR;
    FileNameString = ARRAY FileNameIndex OF CHAR;

  PROCEDURE DoSearch(path : ARRAY OF CHAR;
		     rExp : ARRAY OF CHAR);
    VAR file    : File;
	ch      : CHAR;
        ix      : FileNameIndex;
	ok      : BOOLEAN;
	command, 
	oldName, 
	newName : FileNameString;
  BEGIN
    oldName := "";
    command := "grep -n '";
    Append(rExp,command);
    Append("' ",command);
    Append(path,command);
    PipeInput(command,file,ok);
    ReadByte(file,ch);
   (*
    * pre: a fresh character has been read or EndFile is true
    *)
    WHILE NOT EndFile(file) DO
     (*
      * fetch the file name
      *)
      newName[0] := ch;
      ReadByte(file,ch);
      newName[1] := ch;
      ReadByte(file, ch);               (* Skip C:  *)
      ix := 2;
      WHILE (ch <> ':') AND (ch < 200C) DO
        newName[ix] := ch;
	ReadByte(file,ch);
        INC(ix);
      END;
      newName[ix] := ""; 
      IF Compare(oldName,newName) <> equal THEN
        WriteString("File --- ");
        WriteString(newName); WriteLn;
        oldName := newName;
      END;
     (*
      * now print rest of line
      *)
      ReadByte(file,ch);
      WHILE (ch <> Ascii.lf) AND (ch < 200C) DO
        Write(ch);
        ReadByte(file,ch);
      END;
      WriteLn;
      ReadByte(file,ch); (* post: ch is fresh, or EOF *)
    END;
    ClosePipe(file);
  END DoSearch;

  (* precondition  : pathString is nul terminated and has    *)
  (*                 components separated by colon chars,    *)

  PROCEDURE Lookup(pathString   : ARRAY OF CHAR;
                   regExp       : ARRAY OF CHAR);
    CONST nul      = 0C;
	  dirSep   = "/";
	  pathSep  = ":";
    VAR   pathStr  : MiddleString;
    VAR   ch       : CHAR;
          ix,px    : CARDINAL;
  BEGIN
    px := 0;
    DoSearch("."+dirSep+"*.def",regExp);
    LOOP
      (*
         fetch prefix string
      *)
      ix := 0; ch := pathString[px];
      WHILE (ch <> pathSep) AND (ch <> nul) DO
        pathStr[ix] := ch;
        INC(ix); INC(px);
        IF px > HIGH(pathString) THEN ch := nul;
        ELSE ch := pathString[px];
        END;
      END;
      pathStr[ix] := dirSep; INC(ix);
      pathStr[ix] := "*"; INC(ix);
      pathStr[ix] := "."; INC(ix);
      pathStr[ix] := "d"; INC(ix);
      pathStr[ix] := "e"; INC(ix);
      pathStr[ix] := "f"; INC(ix);
      pathStr[ix] := "";
      (*
         now lookup the file
      *)
(*
WriteLn;
WriteString("looking at ");
WriteString(pathStr);
WriteLn;
*)
      DoSearch(pathStr,regExp);
      IF (px > HIGH(pathString)) OR
         (pathString[px] = nul) THEN (* path ended *)
        RETURN;
      ELSE INC(px);
      END;
    END; (* loop *)
  END Lookup;

  VAR eStr : ShortString;
      pStr : MiddleString;

BEGIN
  IF ArgNumber() <> 2 THEN
    StdError.WriteString("grepdef usage: 'grepdef regexp'");
    StdError.WriteLn;
  ELSE
    GetArg(1,eStr);
    EnvironString("M2SYM",pStr);
    Lookup(pStr,eStr);
  END;
END GrepDef.
