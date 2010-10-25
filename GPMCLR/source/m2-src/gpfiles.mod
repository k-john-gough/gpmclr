
(****************************************************************)
(*                                                              *)
(*         Gardens Point Modula-2 Library Implementation        *)
(*                                                              *)
(*                File name lookup and create			*)
(*                                                              *)
(*     (c) Copyright 1996 Faculty of Information Technology     *)
(*              Queensland University of Technology             *)
(*                                                              *)
(*     Permission is granted to use, copy and change this       *)
(*     program as long as the copyright message is left intact  *)
(*                                                              *)
(*      original module : kjg July 1992				*)
(*      modifications   : pms December 1993 Added changes for   *)
(*                                          Windows NT.         *)
(*                        pms January 1994 Truncate file name   *)
(*                                         extensions to 3 chars*)
(*                        pms 02-Mar-94 Fix call to parameter   *)
(*                                      to MakeLowerName        *)
(*                                                              *)
(****************************************************************
$Log: gpfiles.mpp,v $
Revision 1.1  1996/09/06 07:49:16  lederman
Initial revision

*)



IMPLEMENTATION MODULE GpFiles;

  FROM UxFiles IMPORT 
	File, OpenMode, Open, Create;

  FROM PathLookup IMPORT FindAndOpen;

  FROM ProgArgs IMPORT EnvironString;

(*
 *  IMPORT StdError;
 *
 * 
 *	this module implements the gpm file lookup strategy
 *	it was introduced to make the change from lower case
 *	to mixed case file names in a consistent manner for
 *	gpm, build, gpmake, gpscript, decode, and all other
 *	tools which look up files based on module names.
 *)

  TYPE  FileNameString = ARRAY [0 .. 255] OF CHAR;

  VAR   lowerCase : BOOLEAN;	(* case flag for created files *)

    PROCEDURE MakeLowerCase(VAR s : ARRAY OF CHAR);
      VAR index : CARDINAL; 
	  ch    : CHAR;
    BEGIN
      index := 0; 
      ch := s[index];
      WHILE ch <> "" DO
        IF (ch >= "A") AND (ch <= "Z") THEN
          s[index] := CHR(ORD(ch) + 40B);
        END;
        INC(index); 
	ch := s[index];
      END;
    END MakeLowerCase;

    PROCEDURE ShortenName(VAR name : ARRAY OF CHAR);
      VAR ix,jx,bl : CARDINAL;
    BEGIN
      ix := LENGTH(name);
      bl := ix;		(* index of nul char *)
      FOR jx := ix TO 0 BY -1 DO
	IF name[jx] = "." THEN bl := jx END;
      END;
      (* Truncate file name extensions *)
      (* Was previously only for Windows NT, but now for all versions *)
      IF (ix -bl) > 4 THEN name[bl+4] := 0C END;
      IF bl > oldFileNameLength THEN
       (*
	*   shorten filename by deleting all characters
	*   between oldFileNameLegth and the first dot
	*)
	FOR jx := bl TO ix DO
	  name[jx - bl + oldFileNameLength] := name[jx];
	END;
      (* else leave it all unchanged *)
      END;
    END ShortenName;

    PROCEDURE MakeFilename(	base : ARRAY OF CHAR;
				ext  : ARRAY OF CHAR;
			    VAR name : ARRAY OF CHAR);
      VAR ix,jx : CARDINAL;
	  ok    : BOOLEAN;
    BEGIN
      ix := 0;
      jx := 0;
      WHILE (ix <= HIGH(base)) AND
	    (base[ix] <> "") DO     (* copy up to nul *)
	name[ix] := base[ix]; INC(ix);
      END;
      IF ix > fileNameLength THEN 
	ix := fileNameLength;       (* trim to length *)
      END;
      IF ext[0] <> "" THEN
        name[ix] := "."; INC(ix);   (* insert sep'tor *)
        WHILE (jx <= HIGH(ext)) AND
		(ext[jx] <> "") DO  (* copy up to nul *)
	  name[ix] := ext[jx]; 
	  INC(jx); INC(ix);
        END; 
      END;
      name[ix] := "";		    (* insert trm'tor *)
    END MakeFilename;

    PROCEDURE GpFilename(	base : ARRAY OF CHAR;
				ext  : ARRAY OF CHAR;
			    VAR name : ARRAY OF CHAR);
    BEGIN
      MakeFilename(base,ext,name);
      IF lowerCase THEN MakeLowerCase(name) END;
    END GpFilename;

    PROCEDURE GpCreateFile(	base : ARRAY OF CHAR;
				ext  : ARRAY OF CHAR;
			    VAR name : ARRAY OF CHAR;
			    VAR file : File);	(* NIL if can't create *)
      VAR ok : BOOLEAN;
    BEGIN
      GpFilename(base,ext,name);
      Create(file,name,ok);
      IF NOT ok THEN
         ShortenName (name);
         Create (file, name, ok);
         IF NOT ok THEN file := NIL END;
      END;
    END GpCreateFile;

    PROCEDURE GpFindOnPath(	path : ARRAY OF CHAR;
				base : ARRAY OF CHAR;
				ext  : ARRAY OF CHAR;
			    VAR name : ARRAY OF CHAR;
			    VAR file : File);	(* or NIL if not found *)

      VAR work  : FileNameString;  (* this workstring is needed, since *)
				   (* DoLookup clobbers its outArg ... *)

      PROCEDURE DoLookup(VAR outF : File;
			 VAR inNm : FileNameString;
			 VAR outN : ARRAY OF CHAR);
        VAR ok  : BOOLEAN;
        VAR ch  : CHAR;
	    idx : CARDINAL;
      BEGIN
	file := NIL;
        Open(outF,inNm,ReadOnly,ok);
        IF ok THEN 
          idx := 0;
          REPEAT
	    ch := inNm[idx];
	    outN[idx] := ch;
	    INC(idx);
	  UNTIL ch = "";
	ELSE FindAndOpen(path,inNm,outN,file);
	END;
      END DoLookup;

    BEGIN
      GpFilename(base,ext,work);
     (*
      *   step one, try to find the default name ...
      *)
      DoLookup(file,work,name);
      IF file <> NIL THEN RETURN END;         (* !!!! early exit !!!! *)
     (*
      *   step two, try to find name other case ...
      *)
     (* Other case not needed for Microsoft systems *)
     (*
      *   step three, did it come from DOS ???
      *)
      IF lowerCase THEN MakeLowerCase(work) END;
      ShortenName(work);
      DoLookup(file,work,name);
      IF file <> NIL THEN RETURN END;         (* !!!! early exit !!!! *)
     (*
      *  Oh shucks! failed again ...
      *)
      name[0] := "";
      file := NIL;
    END GpFindOnPath;

    PROCEDURE GpFindLocal(	base : ARRAY OF CHAR;
				ext  : ARRAY OF CHAR;
			    VAR name : ARRAY OF CHAR;
			    VAR file : File);	(* or NIL if not found *)
      VAR ok  : BOOLEAN;
    BEGIN
      GpFilename(base,ext,name);
     (*
      *   step one, try to find the default name ...
      *)
      Open(file,name,ReadOnly,ok);
      IF ok THEN RETURN END; 		   (* !!!! early exit !!!! *)
     (*
      *   step two, try to find name other case ...
      *)
     (* Other case not needed for Microsoft systems *)
     (*
      *   step three, did it come from DOS ???
      *)
      IF lowerCase THEN MakeLowerCase(name) END;
      ShortenName(name);
      Open(file,name,ReadOnly,ok);
      IF ok THEN RETURN END; 		   (* !!!! early exit !!!! *)
     (*
      *  Oh shucks! failed again ...
      *)
      name[0] := "";
      file := NIL;
    END GpFindLocal;

  VAR str : ARRAY [0 .. 256] OF CHAR;

BEGIN
  (*  
   * Ignore GPNAMES=MIXED on Windows NT -> Create is case sensitive
   *                                    -> Open is not
   *)
  lowerCase := TRUE;
END GpFiles.


