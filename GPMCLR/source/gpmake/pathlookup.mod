(*
 * =========== macro processed output from MPP  ==========
 *
 * input file  : pathlookup.mpp
 * time stamp  : 2004:01:10::07:22:58
 *
 * output file : pathlookup.mod
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
(*         Gardens Point Modula-2 Library Implementation        *)
(*                                                              *)
(*                                                              *)
(*     (c) Copyright 1996 Faculty of Information Technology     *)
(*              Queensland University of Technology             *)
(*                                                              *)
(*     Permission is granted to use, copy and change this       *)
(*     program as long as the copyright message is left intact  *)
(*                                                              *)
(****************************************************************)


IMPLEMENTATION MODULE PathLookup;

  FROM UxFiles IMPORT File, Open, OpenMode, GetMode, FileMode;
  FROM Ascii   IMPORT ht;


  (* precondition  : pathString is nul terminated and has    *)
  (*                 components separated by colon chars,    *)
  (*                 openName is long enough for pathname    *)
  (* postcondition : openFile <> NIL ==> file was found.     *)
  (*                 openName has nul terminated absolute    *)
  (*                 path name, or nul string if not found   *)

  CONST
      PathSep = ";";  (* Windows constants *)
      DirSep  = "\";
      Blank   = " ";           
      Tab     = ht;


  PROCEDURE Trim(VAR base : ARRAY OF CHAR);
    VAR indx : CARDINAL;
        myCh : CHAR;
  BEGIN
    indx := 0;
    REPEAT myCh := base[indx]; INC(indx);
    UNTIL (myCh = "") OR (indx > HIGH(base));
    REPEAT DEC(indx); myCh := base[indx]; 
    UNTIL (myCh > " ") OR (indx = 0);
    IF indx < HIGH(base) THEN base[indx+1] := "" END;
  END Trim;

  PROCEDURE FindAndOpen(pathString   : ARRAY OF CHAR;
                        baseName     : ARRAY OF CHAR;
                        VAR openName : ARRAY OF CHAR;
                        VAR openFile : File);
    CONST nul      = 0C;
    VAR   ch       : CHAR;
          found    : BOOLEAN;
          ix,px,bx : CARDINAL;
  BEGIN
    px := 0;
    LOOP
      (*
       * fetch prefix string
      *)
      ix := 0; ch := pathString[px];
      WHILE (ch <> PathSep) AND (ch <> nul) DO
        IF (ch <> Blank) AND (ch <> Tab) THEN
           (* Skip embedded white space in the path string *)
           openName[ix] := ch;
           INC(ix); 
        END;
        INC(px);
        IF px > HIGH(pathString) THEN ch := nul;
        ELSE ch := pathString[px];
        END;
      END;
      IF (ix > 0) AND (openName[ix-1] <> DirSep) THEN
        openName[ix] := DirSep; INC(ix);
      END;
     (*
      * add base name string
      *)
      Trim(baseName);
      bx := 0; ch := baseName[bx];
      WHILE ch <> nul DO
        openName[ix] := ch;
        INC(ix); INC(bx);
        IF bx > HIGH(baseName) THEN ch := nul;
        ELSE ch := baseName[bx];
        END;
      END;
      openName[ix] := nul;
      (*
       * now lookup the file
      *)
      Open(openFile,openName,ReadOnly,found);
      IF found THEN RETURN;
      ELSIF (px > HIGH(pathString)) OR
	    (pathString[px] = nul) THEN (* path ended *)
        openName[0] := nul; RETURN;
      ELSE INC(px);
      END;
    END; (* loop *)
  END FindAndOpen;

  (* precondition  : pathString is nul terminated and has    *)
  (*                 components separated by colon chars,    *)
  (*                 openName is long enough for pathname    *)
  (* postcondition : found = TRUE ==> file was found.        *)
  (*                 openName has nul terminated absolute    *)
  (*                 path name, or nul string if not found   *)

  PROCEDURE FindAbsName(pathString   : ARRAY OF CHAR;
                        baseName     : ARRAY OF CHAR;
                        VAR openName : ARRAY OF CHAR;
                        VAR found    : BOOLEAN);
    CONST nul      = 0C;
    VAR   ch       : CHAR;
          ix,px,bx : CARDINAL;
	  perm     : FileMode;
  BEGIN
    px := 0;
    LOOP
      (*
       * fetch prefix string
      *)
      ix := 0; ch := pathString[px];
      WHILE (ch <> PathSep) AND (ch <> nul) DO
        IF (ch <> Blank) AND (ch <> Tab) THEN
           (* Skip embedded white space in the path string *)
           openName[ix] := ch;
           INC(ix); 
        END;
        INC(px);
        IF px > HIGH(pathString) THEN ch := nul;
        ELSE ch := pathString[px];
        END;
      END;
      IF (ix > 0) AND (openName[ix-1] <> DirSep) THEN
        openName[ix] := DirSep; INC(ix);
      END;
     (*
      *  add base name string
      *)
      Trim(baseName);
      bx := 0; ch := baseName[bx];
      WHILE ch <> nul DO
        openName[ix] := ch;
        INC(ix); INC(bx);
        IF bx > HIGH(baseName) THEN ch := nul;
        ELSE ch := baseName[bx];
        END;
      END;
      openName[ix] := nul;
      (*
       * now lookup the file
      *)
      GetMode(openName,perm,found);
      IF found THEN RETURN;
      ELSIF (px > HIGH(pathString)) OR
	    (pathString[px] = nul) THEN (* path ended *)
        openName[0] := nul; RETURN;
      ELSE INC(px);
      END;
    END; (* loop *)
  END FindAbsName;

END PathLookup.
