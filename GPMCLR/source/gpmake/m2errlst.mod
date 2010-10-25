(*
 * =========== macro processed output from MPP  ==========
 *
 * input file  : m2errlst.mpp
 * time stamp  : 2004:01:09::02:03:04
 *
 * output file : m2errlst.mod
 * created at  : 2004:01:12::14:21:43
 *
 * options ... :  /Ddotnet86
 *
 * =======================================================
 *)

(* -- RCS Header --
		$Log:	m2errlst.mpp,v $
Revision 1.3  94/03/02  15:01:12  mboss
Changed error list file to m2errlst.dat, same as pc and native code.

Revision 1.2  94/02/28  14:10:05  mboss
Increased file size and index size

Revision 1.1  94/01/12  15:37:13  mboss
Initial revision

*)

(* 
 *  extracted with 
 * 	    "opsys" == "windows"
 * 	   "endian" == "little"
 *	"processor" == "iap386"
 *)

(*=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-*)
(* This is the utility program which takes the error    *)
(* message file for Gardens Point Modula and processes  *)
(* it into the form necessary for use by M2InOut        *)

(* Format of the text file is:                          *)
(*      textFile = {comment | message} nul.             *)
(*      comment  = 'line not starting with number'.     *)
(*      message  = number errMess.                      *)
(*      number   = 'an ascii decimal number'.           *)

(* Format of the output table is:                       *)
(*      outTable = index textFile.                      *)
(*      index    = ARRAY[0 .. 512] OF CARDINAL;         *)
(* each index entry is an index into the output table   *)
(* and indexes the corresponding number.errMess string  *)
(*=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-*)

MODULE M2ErrLst;

(*
 *  Revisions:
 *
 *  24-Mar-92  jrh  Remove 'old' format
 *		  (input m2errs.txt -> output m2errlst.dat);
 *		  'new' format with verbose error message text is
 *		  input errmess.txt -> output m2errlst.dat2.
 *  12-Nov-92  jrh  Further size increase.
 *  28-Feb-94  pms  Further size and index increase 5300 & 600
 *  02-Mar-94  pms  Error list file now m2errlst.dat same as pc and native code.
 *
 *)

  IMPORT SYSTEM, Types;
  FROM Terminal IMPORT WriteString, WriteLn, Write, WriteCard;
  FROM ProgArgs IMPORT UNIXexit, EnvironString;
  FROM PathLookup IMPORT FindAndOpen;
  FROM UxFiles IMPORT Open, OpenMode, Create, Close,
             ReadNBytes, WriteByte, File;

  CONST bytesInWord = 4;
  CONST eol      = 12C;
        fileSize = 53000; (* >= bytes in m2errs.txt *)
        indexSiz = 600;
        chrStart = indexSiz * bytesInWord;
        totalSiz = chrStart + fileSize; (*  9000 @ 10-Apr-89 *)
					(* 10000 @ 16-Aug-89 *)
					(* 50000      Mar-92 *)
					(* 52048      Nov-92 *)
                                        (* 55400      Mar-94 *)

  VAR   ch    : CHAR;
        ok    : BOOLEAN;
        read  : CARDINAL;
        ix,lx : CARDINAL;
        total : CARDINAL;
        table : RECORD
                  CASE (* no tag *) : BOOLEAN OF
                  | TRUE  : index : ARRAY [1 .. indexSiz] OF Types.Card32;
                  | FALSE : chars : ARRAY [0 .. totalSiz] OF CHAR;
                  END;
                END;
        pathStr, absName : ARRAY [0 .. 131] OF CHAR;
        errFile, outFile : File;

BEGIN
  FindAndOpen(".","m2errs.txt",absName,errFile);
  IF errFile = NIL THEN
    EnvironString("PATH",pathStr);
    FindAndOpen(pathStr,"m2errs.txt",absName,errFile);
  END;
  IF errFile <> NIL THEN
    WriteString("Reading ");
    WriteString(absName); WriteLn;
  ELSE
    WriteString("**** m2errs.txt not found ****");
    WriteLn; UNIXexit(1);
  END;
  FOR ix := 1 TO indexSiz DO table.index[ix] := 0 END;
  Create(outFile,"m2errlst.dat",ok);
  IF NOT ok THEN
    WriteString("**** Can't create m2errlst.dat ****");
    WriteLn; UNIXexit(1);
  END;
  ReadNBytes(errFile,
             SYSTEM.ADR(table.chars[chrStart]),
             fileSize,
             read);
  Close(errFile,ok);
  ix := chrStart;
  ch := table.chars[ix];
  WHILE ch <> 0C DO (* another line *)
    lx := ix;
    WHILE ch = " " DO (* skip leading blanks *)
      INC(ix); ch := table.chars[ix];
    END;
    (*
       now, is there a number starting the line?
    *)
    IF ("0" <= ch) AND (ch <= "9") THEN
      total := 0;
      WHILE ("0" <= ch) AND (ch <= "9") DO
        total := total * 10 + ORD(ch) - ORD("0");
        INC(ix); ch := table.chars[ix];
      END;
      table.index[total] := lx;        
    END;
    (*
       now find end of line
    *)
    WHILE (ch <> eol) AND (ch <> 0C) DO
      INC(ix); ch := table.chars[ix];
    END;
    IF ch = eol THEN INC(ix); ch := table.chars[ix] END;
  END; (* while *)  
  FOR ix := 0 TO chrStart + read DO 
    WriteByte(outFile,table.chars[ix]);
  END;
  Close(outFile,ok);
END M2ErrLst.

