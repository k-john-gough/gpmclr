(*
 * =========== macro processed output from MPP  ==========
 *
 * input file  : gpscript.mpp
 * time stamp  : 2004:01:11::11:00:28
 *
 * output file : gpscript.mod
 * created at  : 2004:01:12::14:21:43
 *
 * options ... :  /Ddotnet86
 *
 * =======================================================
 *)

(* -- RCS header --
	$Log:	gpscript.mpp,v $
Revision 1.2  93/11/03  08:59:28  mboss
Added DEC Alpha changes

Revision 1.1  93/03/25  14:31:35  mboss
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
(*                Modula-2 Compiler Source Module               *)
(*                                                              *)
(*                The Make Facility - PC Version                *)
(*                 Calls Graph Builder Program                  *)
(*                                                              *)
(*     This program is used by the gpmake driver program.       *)
(*	  Modified from GraphBuild.mod by kjg, Nov 1991		*)
(*                                                              *)
(*        original module : dwc October 1991                    *)
(*        modifications   : jrh Apr 1992  path strings 256 char *)
(*					  check EnvironString	*)
(*			    jrh Apr 1992  Summary if gpm -V	*)
(*			    jrh Apr 1992  message if no DEF/IMP	*)
(*                      : kjg 03-Aug-92 uses new GpFiles procs  *)
(*                      : kjg 03-Nov-04 Version for CLR         *)
(*                                                              *)
(****************************************************************)




MODULE GPScript;

IMPORT Types, StdError;
FROM SYSTEM IMPORT CAST, BYTE;
FROM Ascii IMPORT nul, lf;
FROM Storage IMPORT ALLOCATE;
FROM GenSequenceSupport IMPORT 
	Sequence, ElemPtr, InitCursor, InitSequence, LengthOf,
	GetNext, GetFirst, Ended, LinkLeft, LinkRight, NextIsLast;
FROM MkAlphabets IMPORT 
	TermSymbols, HashBucketType, SymbolSet, FileNameType;
FROM MkInOut IMPORT 
	middleMax,
	MiddleString, ShortString, FileNameString, SetAppName,
	OpenInput, OpenDefOrModFile, CloseDefOrModFile, DiagName,
	CreateMakFile, CloseMakFile, WriteMb, BaseName,
	OpenSymFile, CloseSymFile, AbortMessage;
FROM MkScanner IMPORT 
	InitScanner, symbol, lexAtt, GetSymbol,
	InitSymScan, symSmbl, GetSymSmbl;
FROM MkNameHandler IMPORT 
	sysBkt, foreignBkt, directBkt,
	GetSourceRep, MakeFileName,
	FindFileName,
	Summary;
FROM ProgArgs IMPORT EnvironString, ArgNumber, GetArg, Assert, UNIXexit;
FROM UxFiles IMPORT 
	Create, WriteByte, Open, Close, File, ModifyTime, OpenMode;

CONST
  afterImports = SymbolSet{varSy, endSy, constSy, typeSy, procedureSy,
                           eofSy, beginSy, moduleSy};
  importDecs = SymbolSet{importSy, fromSy};  

  usageStr = "Usage: GPScript [(-|/)+acdfgIilO[012]mprStvVX] BaseModFileName";
  usage2   = "           -+ causes GPMake to chatter about progress";
  usage3   = "           -S (non CLR) calls build with Build -s";
  usage4   = "           -c creates CLR program executables";
  usage5   = "          ... other options are for GPM";

TYPE
  ModRecPtr = POINTER TO ModRec;
  ModRec = RECORD
             name    : HashBucketType;
             imports : Sequence;
	     magic   : CARDINAL;
             class   : FileNameType;
	     done    : BOOLEAN;
	     absNam  : FileNameString;
           END;

VAR
  toDoList : Sequence;
  modRec, current, dummy : ModRecPtr;
  prevCurs, modCurs : ElemPtr;
  argStr  : ShortString;
  gpmArgs : ShortString;
  filName, makName : FileNameString;
  index, argN : CARDINAL;
  baseHash : HashBucketType;
  baseName : FileNameString;
  exeFound : BOOLEAN;
  modFound : BOOLEAN;
  explain  : BOOLEAN;
  clrTarget : BOOLEAN;

(* ======================================================================== *)

  PROCEDURE Usage;
  BEGIN
    StdError.WriteString(usageStr); StdError.WriteLn;
    StdError.WriteString(usage2);   StdError.WriteLn;
    StdError.WriteString(usage3);   StdError.WriteLn;
    StdError.WriteString(usage4);   StdError.WriteLn;
    StdError.WriteString(usage5);   StdError.WriteLn;
    UNIXexit(1);
  END Usage;

(* ======================================================================== *)

PROCEDURE CreateModRec(VAR mod : ModRecPtr;
			   nam : HashBucketType;
			   cls : FileNameType);
BEGIN
  NEW(mod);
  WITH mod^ DO
    name := nam;
    InitSequence (imports);
    class := cls;
    magic := 0;
    done := FALSE;
  END;
END CreateModRec;


PROCEDURE WriteMakString(s : ARRAY OF CHAR);
  VAR i : Types.SHORTCARD;
BEGIN
  i := 0;
  WHILE s[i] <> "" DO WriteMb(s[i]); INC(i) END;
END WriteMakString;

PROCEDURE WriteMbLn();
BEGIN
  WriteMb(lf);
END WriteMbLn;

PROCEDURE OutputModule (VAR module : ModRecPtr);
(* See comment below
VAR
  moduleName : FileNameString;
  index : CARDINAL;
*)
BEGIN
  IF NOT module^.done THEN
    IF module^.class = syx THEN RETURN END;
    WriteMakString("gpx ");
    WriteMakString(gpmArgs);
    WriteMb(" ");
(* PC version was:
 *  index := 0;
 *  GetSourceRep(module^.name,moduleName,index);
 *  moduleName[8] := "";
 *  WriteMakString(moduleName);
 *  IF module^.class = def THEN
 *    WriteMakString(".def");
 *  ELSIF module^.class = mod THEN
 *    WriteMakString(".mod");
 *  END;
 *	instead of following line and other use of absNam.
 *	graphbuild does not use absNam. 
 *)
    WriteMakString(module^.absNam);
    WriteMbLn();
    module^.done := TRUE;
  END;
END OutputModule;

PROCEDURE SearchKnownList(modName : HashBucketType; 
			VAR found : BOOLEAN;
                	VAR item  : ModRecPtr);
VAR
  curs : ElemPtr;
BEGIN
  found := FALSE;
  InitCursor(toDoList,curs);
  WHILE (NOT found AND NOT Ended(curs)) DO
    GetNext(curs,item);
    found := (modName = item^.name) AND 
		((item^.class = def) OR
		 (item^.class = syx));
  END;
END SearchKnownList; 

PROCEDURE UpdateGraph (defName : HashBucketType; current : ModRecPtr);
VAR
  defRec, modRec : ModRecPtr;
  symName  : MiddleString;
  nameArr  : FileNameString;
  found    : BOOLEAN;
  i        : CARDINAL;
   
BEGIN
  (* =================================================== * 
   *
   *  SYSTEM is special, and does not have a .syx file
   *  so return immediately if import is SYSTEM
   *)
  IF defName = sysBkt THEN RETURN END;
  (* =================================================== *)
  SearchKnownList(defName,found,defRec);
  IF NOT found THEN  
   (*  ============================ *
    *    This is a module which
    *    was previously unknown 
    *  ============================ *)
    FindFileName(defName,def,nameArr,found);
    CreateModRec(defRec,defName,def);
    WITH defRec^ DO
      IF NOT found THEN
        (*  ============================ *
	 *    def not found locally. 
	 *    Look for library .syx 
	 *  ============================ *)
	OpenSymFile(defName,symName,found);
        IF NOT found THEN (* error: symbol file not found *)
          StdError.WriteString("#gpmake: Can't find definition or symbol file for: ");
	  DiagName(defName);
          StdError.WriteLn();
	  UNIXexit(1);
        END;
	class := syx;
        (*  ============================ *
	 *  link behind the to-do cursor
	 *  ============================ *)
        LinkLeft(toDoList,defRec);
        CloseSymFile;
        (*  ============================ *
	 *   But this module might still
	 *   have a local implementation
	 *  ============================ *)
        FindFileName(defName,mod,nameArr,found);
	IF found THEN (* local mod *)
	  CreateModRec(modRec,defName,mod);
	  modRec^.absNam := nameArr;
	  LinkRight(toDoList,modRec);
	END;
      ELSE (* ========================== *
	 *    def was found locally. 
	 *  ============================ *)
        absNam := nameArr;
        LinkRight(toDoList,defRec);
      END; (* if *)
    END; (* with defRec^ *)
  END;  (* if not found on list *)
  LinkRight (current^.imports,defRec); (* must link even if known *)
END UpdateGraph;

(* ------------------------------------------------ *
PROCEDURE WriteImportList(mod : ModRecPtr);
VAR
  curs : ElemPtr;
  item : ModRecPtr;
BEGIN
  DiagName(mod^.name);
  IF mod^.class = def THEN
    ErrOutput.WriteString("(def)");
  END;
  ErrOutput.WriteString(" imports ");
  InitCursor(mod^.imports,curs);
  WHILE NOT Ended(curs) DO
    GetNext(curs,item);
    DiagName(item^.name);
    ErrOutput.Write(" ");
  END;
  ErrOutput.WriteLn;
END WriteImportList;
 * ------------------------------------------------ *)

PROCEDURE GraphDFS (current : ModRecPtr);
(*
 *  depth first search on imports graph
 *)
VAR
  curs : ElemPtr;
  item : ModRecPtr;
BEGIN
  InitCursor(current^.imports,curs);
  WHILE NOT Ended(curs) DO
    GetNext(curs,item);
    IF NOT item^.done THEN
      GraphDFS(item);
    END;
  END;
  OutputModule(current);
END GraphDFS;

PROCEDURE SkipTo (haltSet : SymbolSet);
BEGIN
  WHILE NOT (symbol IN haltSet) DO
    GetSymbol;
  END;
END SkipTo;

PROCEDURE ProcessImportStatement;
BEGIN
  CASE symbol OF
  | fromSy   : GetSymbol;  
               IF symbol <> ident THEN 
		 AbortMessage("invalid source file format","");
                 UNIXexit(1);
               ELSE UpdateGraph (lexAtt.hashIx,current); END;
               GetSymbol;  (* skip IMPORT  *)
               GetSymbol;
  | importSy : GetSymbol;
               IF symbol = implementationSy THEN
                 GetSymbol; (* FROM *)
		 GetSymbol;
                 IF symbol <> litstring THEN 
		   AbortMessage("invalid source file format","");
	           UNIXexit(1);
                 END;
               ELSIF symbol = ident THEN (* multi entries dec-91 kjg *)
                 UpdateGraph (lexAtt.hashIx,current); 
	         GetSymbol;  (* read past comma *)
	         WHILE symbol = comma DO 
		   GetSymbol;
		   IF symbol = ident THEN
		     UpdateGraph (lexAtt.hashIx,current); GetSymbol;
		   END;
		 END; (* while *)
               ELSE 
		 AbortMessage("invalid source file format","");
	         UNIXexit(1);
               END;
  END;  (* case *)
END ProcessImportStatement;

PROCEDURE CheckBldOptions(inArg  : ARRAY OF CHAR;
                      VAR outArg : ARRAY OF CHAR);

    TYPE  CharSet = SET OF [0C .. 177C];

    VAR ix, jx : CARDINAL;
        char   : CHAR;
BEGIN
  ix := 0; jx := 0;
  char := inArg[0];
  WHILE char <> "" DO
    IF char IN CharSet{"-", "g", "v", "V"} THEN
        outArg[jx] := char; INC(jx);
    END;
    INC(ix); char := inArg[ix];
  END;
  outArg[jx] := "";
END CheckBldOptions;

PROCEDURE AppendArg();
  VAR aIx, sIx : [0 .. 127];
      chr      : CHAR;
BEGIN
  sIx := LENGTH(gpmArgs);
  aIx := 1;
  chr := argStr[aIx];
  WHILE chr <> "" DO
    IF chr = "+" THEN explain := TRUE;
    ELSE
      IF (chr = "c") OR (chr = "m") THEN clrTarget := TRUE END;
      gpmArgs[sIx] := chr;
      INC(sIx);
    END;
    INC(aIx);
    chr := argStr[aIx];
  END;
  gpmArgs[sIx] := "";
END AppendArg;
    
BEGIN  (* main  *)
  SetAppName("GPScript");
  clrTarget := FALSE;
  explain   := FALSE;
  argN      := ArgNumber();
  IF argN = 0 THEN Usage() END;
  IF argN > 1 THEN
    gpmArgs := "-";
    FOR index := 0 TO argN - 2 DO
      GetArg(index,argStr);
      IF (argStr[0] = "/") OR (argStr[0] = "-") THEN AppendArg() END;
    END;
  ELSE gpmArgs := "";
  END;
  (*
   *  now follow GraphBuild 
   *)
  InitSequence (toDoList);
  OpenInput;
  InitScanner; 
  IF symbol <> moduleSy THEN 
    AbortMessage("not a base module","");
    UNIXexit(1); 
  END;
  GetSymbol;
  baseHash := lexAtt.hashIx;
  index := 0;
  GetSourceRep(baseHash,baseName,index);
  (*  ======================================= *
   *   create graph node for the base module
   *  ======================================= *)
  CreateModRec(modRec,baseHash,mod);
  BaseName(modRec^.absNam);
  LinkRight(toDoList,modRec);
  InitCursor(toDoList,modCurs); 
  prevCurs := modCurs;
  GetNext(modCurs,current);
  LOOP  (* while still modules on to-do list *)
    SkipTo(importDecs+afterImports);
    WHILE NOT (symbol IN afterImports) DO 
      ProcessImportStatement;
      SkipTo(importDecs+afterImports);
    END; (* while *)
    CloseDefOrModFile;
    IF NextIsLast(prevCurs) THEN EXIT; 
    ELSE
      modCurs := prevCurs;
      GetNext(modCurs,dummy);
      prevCurs := modCurs;
      GetNext(modCurs,current);
    END;
    IF current^.class = def THEN
      MakeFileName(current^.name,def,filName);
    ELSIF current^.class = mod THEN
      MakeFileName(current^.name,mod,filName);
    ELSE Assert(FALSE,"symbol file on to-do list");
    END;
    (*
     *   scan the source file of the next file
     *   on the module to-do list ...
     *)
    OpenDefOrModFile(filName);
    InitScanner;
    IF (symbol = ident) AND ((lexAtt.hashIx = foreignBkt) OR
       (lexAtt.hashIx = directBkt)) THEN
      StdError.WriteString ("Foreign implementation of <");
      DiagName(current^.name);
      StdError.WriteString ("> may need recompilation.");
      StdError.WriteLn;
    ELSIF current^.class = def THEN
      (*
       *  If this is a definition module, then
       *  it is necessary to create a node for 
       *  the implementation module also. At the
       *  least this .mod imports its own .def
       *)
      CreateModRec(modRec,current^.name,mod);
      FindFileName(current^.name,mod,modRec^.absNam,modFound);
      LinkRight(toDoList,modRec);
    END;
    SkipTo(SymbolSet{implementationSy,definitionSy});
    IF symbol = eofSy THEN
      StdError.WriteString(
                  '#gpmake: "DEFINITION" or "IMPLEMENTATION" not found');
      StdError.WriteString(" in file ");
      StdError.WriteString(filName);
      StdError.WriteLn();
      UNIXexit(1);
    END;
    GetSymbol;  (* skip MODULE *)
    GetSymbol;
    IF lexAtt.hashIx <> current^.name THEN
      StdError.WriteString("#gpmake: searching for <");
      DiagName(current^.name);
      StdError.WriteString(">, found <");
      DiagName(lexAtt.hashIx);
      StdError.WriteString("> in file ");
      StdError.WriteString(filName);
      StdError.WriteLn();
      UNIXexit(1);
    END;
  END;
  (* Graph Built  *)
  (*
   *  In this case the Make file is an ascii file
   *)
  IF clrTarget THEN
    MakeFileName(baseHash,bat,makName);
    CreateMakFile(makName);
    WriteMakString("REM script for build of module <");
  ELSE
    MakeFileName(baseHash,mak,makName);
    CreateMakFile(makName);
    WriteMakString("# script for build of module <");
  END;
  WriteMakString(baseName);
  WriteMb(">");
  WriteMbLn();
  InitCursor(toDoList,modCurs);
  WHILE NOT Ended(modCurs) DO
    GetNext(modCurs,current);
    IF current^.class = mod THEN
      GraphDFS(current);
    END;
  END;
  IF NOT clrTarget THEN
    CheckBldOptions(gpmArgs,gpmArgs);
    WriteMakString("build ");
    IF (gpmArgs[0] <> "") AND 
       (gpmArgs[1] <> "") THEN
      WriteMakString(gpmArgs);
      WriteMb(" ");
    END;
    WriteMakString(baseName);
    WriteMbLn();
  END;
  CloseMakFile;
  IF explain THEN Summary() END;
  StdError.WriteString('Script output file is "');
  StdError.WriteString(makName);
  StdError.Write('"');
  StdError.WriteLn;
  UNIXexit(0);
END GPScript.
