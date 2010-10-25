(*
 * =========== macro processed output from MPP  ==========
 *
 * input file  : decider.mpp
 * time stamp  : 2004:01:08::03:51:26
 *
 * output file : decider.mod
 * created at  : 2004:01:12::15:03:24
 *
 * options ... :  /Ddotnet86
 *
 * =======================================================
 *)

(* -- RCS header --
	$Log:	decider.mpp,v $
Revision 1.4  94/01/14  10:48:51  mboss
Added Windows NT changes.

Revision 1.3  93/11/03  08:59:04  mboss
Added DEC Alpha changes

Revision 1.2  93/06/14  13:07:28  mboss
Check if executable is up to date, so no need for build.
When a mod file is found to not need recompilation, use its object file
time to update the latest object time; when all recompilations are done,
check executable time against latest object, and if later, return new code
3 to gpmake

Revision 1.1  93/03/25  14:31:07  mboss
Initial revision

*)
(* 
 *  extracted with 
 * 	    "opsys" == "windows"
 * 	   "endian" == "little"
 *	"processor" == "iap386"
 *)

(****************************************************************)
(*                                                              *)
(*                Modula-2 Compiler Source Module      	        *)
(*                                                              *)
(*                The Make Facility - PC Version       	        *)
(*			Decider program				*)
(*                                                              *)
(*     This program is used by the gpmake driver program.       *)
(*                                                              *)
(*        original module : kjg july 1987              	        *)
(*        modifications : kjg 03-Aug-92 uses new GpFiles procs  *)
(*			  jrh 04-Dec-92 UxFiles / scan problem	*)
(*			  jrh 14-Jun-93 No build if up to date	*)
(*                        pms 29-Oct-93 Added Alpha changes     *) 
(*                        pms 13-Jan-94 Added Windows NT changes*)
(*                        kjg 08-Jan-04 Added CLR changes       *)
(*                                                              *)
(****************************************************************)




MODULE Decider;

IMPORT StdError;

FROM Ascii IMPORT nul;
FROM SYSTEM IMPORT BYTE,CAST;
FROM UxFiles IMPORT ModifyTime;
FROM Storage IMPORT ALLOCATE;
FROM GenSequenceSupport IMPORT 
	Sequence, InitSequence, ElemPtr, GetNext,
	InitCursor, Ended, LinkRight;
FROM MkAlphabets IMPORT 
	TermSymbols, HashBucketType, SymbolSet, FileNameType;
FROM MkScanner IMPORT 
	GetSymSmbl, InitSymScan, symSmbl, lexAtt,
        GetMakSmbl, InitMakScan, makSmbl;
FROM MkNameHandler IMPORT 
	FindFileName,
	MakeFileName, GetSourceRep;
FROM MkInOut IMPORT 
	ShortString, FileNameString, MiddleString,
	OpenSymFile, OpenMakFile, WriteMb, OpenRefFile, DiagName,
	GetMakSymPos, GetMakFilePos, SetMakFilePos, SetAppName,
	CloseSymFile, CloseRefFile, WriteStringToTempFile;
FROM ProgArgs IMPORT Assert, UNIXexit, UNIXtime;

(* Script file :
 *   beginSy ident {(definitionSy|moduleSy} ident (exceptSy|fixNum)} endSy.
 *)
(* exit codes = 
 *      0 = ready to build;
 *      1 = needs recompilation;
 *      2 = error detected;
 *      3 = no action needed (executable up to date)
 *)

TYPE
  ModInfoRec = RECORD
		 name : HashBucketType;
		 magic : CARDINAL;
               END;

  ModInfoPtr = POINTER TO ModInfoRec; 

  TrickWord = RECORD
		CASE : BOOLEAN OF
		| TRUE : card : CARDINAL;
		| FALSE : b0,b1,b2,b3 : BYTE;
                END;
              END;

VAR
  now  : CARDINAL;	(* UNIXtime at start of make *)
  mods : Sequence;
  baseHash, currName : HashBucketType;
  baseName : FileNameString;
  currType : FileNameType;
  currMod : ModInfoPtr;
  outName : FileNameString;
  errStr : ShortString;
  exCode, index, mark, currPos : CARDINAL;
  card : CARDINAL;
  magNum : TrickWord;
  latestObj: CARDINAL;
  objName : FileNameString;
  objTime : CARDINAL;
  ok : BOOLEAN;
  exeTime : CARDINAL;

(* =================================================================== *)

CONST mkFilErr = "invalid make file format";
      syFilErr = "invalid symbol file format";

PROCEDURE Check(cond : BOOLEAN; str : ARRAY OF CHAR);
  VAR ix : CARDINAL;
BEGIN
  IF NOT cond THEN
    FOR ix := 0 TO HIGH(str) DO errStr[ix] := str[ix] END;
    exCode := 2;
  END;
END Check;

PROCEDURE GetMagicNumber (nam : HashBucketType; 
			  VAR magicNum : CARDINAL;
			  VAR found : BOOLEAN);
VAR
  curs : ElemPtr;
  mod : ModInfoPtr;
BEGIN
  magicNum := 0;
  found := FALSE;
  InitCursor(mods,curs);
  WHILE NOT Ended(curs) AND NOT found DO
    GetNext(curs,mod);
    IF mod^.name = nam THEN
      magicNum := mod^.magic;
      found := TRUE;
    END;
  END;
END GetMagicNumber;

PROCEDURE MoreRecent(lhName : ARRAY OF CHAR;
		     rhName : ARRAY OF CHAR) : BOOLEAN;
  VAR lhTime, rhTime : CARDINAL;
      found : BOOLEAN;
BEGIN
  (*
   *  guard against the possibility that the 
   *  source is newer than "now" which would
   *  otherwise cause repeated recompilation
   *
   *     RETURN "more recent" AND NOT "just done"
   *)
  ModifyTime(lhName,lhTime,found);
  ModifyTime(rhName,rhTime,found);
  RETURN (lhTime > rhTime) AND
	NOT ((lhTime > now) AND
	     (rhTime > now - 30));
END MoreRecent;

PROCEDURE TimesDiffer(lhName : ARRAY OF CHAR;
		      rhName : ARRAY OF CHAR) : BOOLEAN;
  VAR lhTime, rhTime : CARDINAL;
      foundL, foundR : BOOLEAN;
BEGIN
  ModifyTime(lhName,lhTime,foundL);
  ModifyTime(rhName,rhTime,foundR);
  (*
   *  no matter how different rhTime and lhTime are, if
   *  rhTime is newer than "now" no recompilation will
   *  be done. This guards against repeats on slow iron
   *)
  RETURN NOT foundR 
      OR NOT foundL
      OR
         (rhTime < now) AND
	 (ABS(VAL(INTEGER,lhTime) - VAL(INTEGER,rhTime)) > 60);
END TimesDiffer;

PROCEDURE CheckSymFile (name : HashBucketType; 
			VAR redo : BOOLEAN;
			VAR magicNum : CARDINAL);
(*
 * Need to redo if   1. syx file does not exist  OR
 *		     2. keys on imports are inconsistent  OR
 *		     3. def file is newer than syx file
 * 
 * SymFile = Header ModuleImports SymbolModule ImportOjbects eofSy.
 * Header = VersionNumber DefModName.
 * ModuleImports = lBrac {ident ModuleKey} rBrac.
 * SymbolModule = moduleSy {Definition} endSy.
 *)

VAR
  ok, found : BOOLEAN;
  mNum : CARDINAL;
  symName : MiddleString;
BEGIN
  redo := FALSE;
  FindFileName(name,def,outName,ok);	(* outname is defName *)
  (*
   *  The sym file should be local, since the 
   *  def file is known to be a local file.
   *  However, looking up on the path will 
   *  not hurt here as the linker doesn't 
   *  need to know where the symbol file is.
   *  OpenSymFile does a lookup on the path.
   *)
  (*
   *  pms 13-Jan-94
   *  WRONG !!!!  looking on he path does hurt as it may be on 
   *  the path and more recent.  in that case we pick up an syx file that
   *  bears no relation to a local def file, which is never compiled. 
   *  Only OpenSymFile if we really do find it locally.
   *)
  FindFileName(name,syx,symName,ok);
  IF NOT ok THEN
    redo := TRUE; 
  ELSE
    IF MoreRecent(outName,symName) THEN  (* .def newer than .syx *)
      redo := TRUE;
    ELSE
      OpenSymFile(name,symName,ok);
      InitSymScan;
      (* skip to start of imports *)
      WHILE NOT (symSmbl IN SymbolSet{lBrac,keySy}) DO GetSymSmbl; END;
      IF symSmbl = lBrac THEN 
        GetSymSmbl;  (* read past lBrac *)
        WHILE (symSmbl <> rBrac) AND NOT redo AND (exCode <> 2) DO
          Check(symSmbl = ident,syFilErr);
          GetMagicNumber (lexAtt.hashIx,mNum,found);
          IF found THEN
  	    GetSymSmbl;
            Check(symSmbl = keySy,syFilErr);
            IF mNum <> lexAtt.fixValue THEN  (* keys not consistent *)
	      redo := TRUE;
            ELSE
	      GetSymSmbl;
            END;
	  ELSE (* not found, just skip *)
	    GetSymSmbl; GetSymSmbl;
          END; (* found *)
        END;  (* while *)
      END;  (* if lBrac *)
      IF NOT redo THEN 
        WHILE symSmbl <> keySy DO GetSymSmbl; END;  (* skip to magic num *)
        magicNum := lexAtt.fixValue;
      END;
    END; (* if more recent *)
  END; (* if ok *)
(** ErrOutput.WriteLn; **)
  CloseSymFile;
END CheckSymFile;

PROCEDURE CheckRefFile (name : HashBucketType; VAR redo : BOOLEAN);
VAR
  objName : FileNameString;
  refName : MiddleString;
  mNum : CARDINAL;
  ok, found : BOOLEAN;
BEGIN
  redo := FALSE;
  FindFileName(name,mod,outName,ok);	(* outName is modName *)
  (* jrh  04-Dec-92
   *  UxFiles.ModifyTime has been modified to avoid a problem with empty
   *  file names. Thus it is now safe to discard the results of
   *  FindFileName.
   *)
  FindFileName(name,obj,objName,ok);
  IF NOT ok THEN (* can't find file.dll, look for file.exe instead *)
    FindFileName(name,exe,objName,ok);
  END;
  OpenRefFile(name,refName,ok);
  IF NOT ok THEN
    redo := TRUE; 
  ELSE
    IF  MoreRecent(outName,refName) OR     (* .mod newer than .rfx *)
        TimesDiffer(refName,objName) THEN  (* .obj and .rfx differ *)
      redo := TRUE;
    ELSE
      InitSymScan;
       (*
	*  In the case that this is an implementation 
	*  module it is necessary to check the magic
	*  of the symbol file to see it the last
	*  compilation was consistent ...
	*)
      IF symSmbl = implementationSy THEN (* import own syx *)
        WHILE symSmbl <> keySy DO GetSymSmbl END;
        GetMagicNumber (name,mNum,found);
        IF  found AND 
	    (mNum <> lexAtt.fixValue) THEN  (* keys not consistent *)
	  redo := TRUE;
        END;
      END; (* import own syx *)
      (* now skip to start of imports *)
      WHILE NOT (symSmbl IN SymbolSet{importSy,eofSy}) DO GetSymSmbl; END;
      IF symSmbl = importSy THEN
        GetSymSmbl;  
        WHILE (symSmbl <> endSy) AND NOT redo AND (exCode <> 2) DO
	  Check((symSmbl = ident) OR (symSmbl = litstring),syFilErr);
          IF symSmbl = ident THEN
            GetMagicNumber (lexAtt.hashIx,mNum,found);
            IF found THEN
    	      GetSymSmbl;
	      Check(symSmbl = keySy,syFilErr);
              IF mNum <> lexAtt.fixValue THEN  (* keys not consistent *)
	        redo := TRUE;
              END; (* if keys not consistent *)
	    ELSE GetSymSmbl; (* just skip it *)
            END;  (* found *)
          END; (* symbol = ident *) 
          GetSymSmbl;
        END; (* while *)
      END;  (* if importSy *)
    END; (* if more recent *)
  END; (* if ok ref file *)
(** ErrOutput.WriteLn; **)
  CloseRefFile;
END CheckRefFile;

PROCEDURE NeedsRecomp (name : HashBucketType; 
		       modType : FileNameType; 
		       VAR magicNum : CARDINAL) : BOOLEAN;
VAR
  redo : BOOLEAN;
BEGIN
  IF modType = def THEN
    CheckSymFile(name,redo,magicNum);
  ELSIF modType = mod THEN
    CheckRefFile(name,redo);
  ELSE Assert(FALSE);
  END;
  RETURN (redo);
END NeedsRecomp;

BEGIN  (* main *)
  SetAppName("Decider");
  exCode := 0;
  latestObj := 0;
  OpenMakFile;
  InitMakScan;
  InitSequence(mods);
  Check(makSmbl = beginSy,mkFilErr);
  GetMakSmbl;
  Check(makSmbl = ident,mkFilErr);
  baseHash := lexAtt.hashIx;
  GetMakSmbl;
  Check(makSmbl = fixNum,mkFilErr);
  now := lexAtt.fixValue;
  GetMakSmbl;
  WHILE (makSmbl <> endSy) AND (exCode = 0) DO
    IF makSmbl = definitionSy THEN 
      currType := def; 
    ELSIF makSmbl = moduleSy THEN
      currType := mod;
    ELSIF makSmbl = fromSy THEN
      currType := syx;
    END; 
    GetMakSmbl;
    Check(makSmbl = ident,mkFilErr);
    currName := lexAtt.hashIx;
    mark := GetMakSymPos();
    GetMakSmbl;
    IF makSmbl = fixNum THEN  (* library, or already done *)
      IF currType <> mod THEN  (* add to list for 'later' checks *)
        NEW(currMod);
        WITH currMod^ DO
          name := currName;
          magic := lexAtt.fixValue;
        END;
        LinkRight(mods,currMod);
      ELSE 
	(* currType = mod - don't need to keep info *)
      END;
    ELSIF makSmbl = exceptSy THEN
      IF NeedsRecomp(currName,currType,magNum.card) THEN
        exCode := 1;
      ELSE (* up to date, save data for later checks *)
        IF currType = def THEN  (* enter magic number in file and list *)
          currPos := GetMakFilePos();
          SetMakFilePos(mark);
          WriteMb(fixNum);
	  card := magNum.card; 
	  WriteMb(CHR(card MOD 256)); card := card DIV 256; 
	  WriteMb(CHR(card MOD 256)); card := card DIV 256;
	  WriteMb(CHR(card MOD 256)); card := card DIV 256;
	  WriteMb(CHR(card MOD 256)); card := card DIV 256;
          NEW(currMod);
	  WITH currMod^ DO
	    name := currName;
	    magic := magNum.card;
          END;
	  LinkRight(mods,currMod);
          SetMakFilePos(currPos);
        ELSIF currType = mod THEN  (* check for latest object *)
          FindFileName(currName,obj,objName,ok);
          ModifyTime(objName,objTime,ok);
          IF objTime > latestObj THEN
            latestObj := objTime;
          END;
        END;
      END;   
    ELSE
      Check(FALSE,mkFilErr);
    END; 
    GetMakSmbl;
  END; (* while *)
  IF exCode = 0 THEN 
    (* all recompiled - do we need to build? *)
    FindFileName(baseHash,exe,outName,ok);
    ModifyTime(outName,exeTime,ok);
    IF exeTime > latestObj THEN latestObj := exeTime END;
    IF ok AND (latestObj < now) THEN
      exCode := 3;  (* executable up to date - no build needed *)
    ELSE
(* 
 * was:
 *   MakeFileName(baseHash,exe,outName);
 *  but this relies on the Unix exe extension being empty. So: 
 *)
      index := 0;
      GetSourceRep(baseHash,outName,index);
      outName[index] := nul;
      WriteStringToTempFile(outName);
    END;
  ELSIF exCode = 1 THEN
    WriteStringToTempFile(outName);
  ELSE 
    Assert(exCode = 2); 
    WriteStringToTempFile(errStr);
  END;
  UNIXexit(exCode);
END Decider.
