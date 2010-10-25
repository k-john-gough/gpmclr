
(****************************************************************)
(*                                                              *)
(*              Modula-2 Compiler Source Module                 *)
(*                                                              *)
(*                   Reference File Builder.                    *)
(*                                                              *)
(*    (c) copyright 1988 Faculty of Information Technology.     *)
(*                                                              *)
(*      original module : kjg October 1988                      *)
(*      modifications   :                                       *)
(*                                                              *)
(****************************************************************
$Log: m2reffil.mod,v $
Revision 1.6  1997/01/16 05:51:54  gough
fix bad merge of modifications in last revision.

Revision 1.5  1997/01/16 04:55:08  gough
Make use of the new re-entrant symbol file handling interface.

Revision 1.4  1996/11/27 02:42:51  lederman
force import of EXCEPTIONS if exceptOK is set - needed for rts msgs
also add recursion over module body nestBlks to confirm body is empty

Revision 1.3  1995/10/10 23:33:24  lederman
DCode V3 stuff

# Revision 1.2  1994/07/01  05:23:31  lederman
# import versionNumber from M2Machine
#
# Revision 1.1  1994/04/07  05:13:27  lederman
# Initial revision
#
*****************************************************************)

IMPLEMENTATION MODULE M2RefFile;

  FROM GenSequenceSupport IMPORT
	ElemPtr, Sequence, InitCursor, GetNext, Ended, IsEmpty;
  FROM M2NodeDefs    IMPORT
	IdDesc, globalModList, symKeyValue, modState, 
	IdString, IdNodeClass, thisCompileUnit, Attribute;
  FROM M2InOut       IMPORT
	CreateRefFile, WriteRb, CloseRefFile, OpenOldSymFile, CloseOldSymFile;
  FROM M2Alphabets   IMPORT ModStateFlags, TerminalSymbols, HashBucketType;
  FROM M2NameHandler IMPORT SpellingIndex, DumpBytes, EnterString;
  FROM M2Scanner     IMPORT 
	lexAtt, symSmbl, GetSymSmbl, PshSymScanState, PopSymScanState;
  FROM M2MachineConstants IMPORT bytesInWord, refVersion, exceptOK;

  VAR exceptName : HashBucketType;
      exceptKey  : CARDINAL;

 (*
  * This procedure fudges the import of EXCEPTIONS
  * This is required by all modules if exceptOK = TRUE
  * (since unhandled exceptions end up there)
  *)
  PROCEDURE ImportEXCEPTIONS();
    VAR exceptBkt : HashBucketType;
	ok : BOOLEAN;
  BEGIN
    EnterString("exceptions",exceptBkt);
    OpenOldSymFile(exceptBkt,ok);
    IF ok THEN 
      PshSymScanState;
      GetSymSmbl;
      exceptName := lexAtt.hashIx;
      REPEAT	(* last keySy is module key *)
        GetSymSmbl;
        IF symSmbl = keySy THEN exceptKey := lexAtt.keyValue END;
      UNTIL symSmbl = eofSy;
      PopSymScanState;
    END;
    CloseOldSymFile();
  END ImportEXCEPTIONS;

  PROCEDURE WriteNum(num : CARDINAL);
    VAR ix : CARDINAL;
  BEGIN
    (*
     *   here, the bytes are always written out so
     *   so that the lsb comes first in the file
     *   no matter what the endian value
     *)
     FOR ix := 1 TO bytesInWord DO
      WriteRb(CHR(num MOD 400B)); num := num DIV 400B;
    END;
  END WriteNum;

  PROCEDURE WriteRefFile(callSy : HashBucketType);
    VAR curs : ElemPtr;
        elem : IdDesc;

   (* Check if any nested module text *)
    PROCEDURE NoMods(str : IdString) : BOOLEAN;
      VAR idx : INTEGER;
    BEGIN
      FOR idx := 0 TO HIGH(str) DO
	IF str[idx]^.idClass = modNode THEN 
          WITH str[idx]^.body^ DO
	    RETURN IsEmpty(statements) AND IsEmpty(finalSeq) AND NoMods(nestBlks);
          END;
        END;
      END;
      RETURN TRUE;
    END NoMods;

  BEGIN
    IF exceptOK THEN ImportEXCEPTIONS END;  (* Really part of runtime ? *)

    CreateRefFile(thisCompileUnit^.name);
  (*
   * write out header
   *)
    IF progMod IN modState THEN WriteRb(moduleSy);
    ELSE WriteRb(implementationSy);
    END;
    WriteRb(fixNum);
    IF profiling IN modState THEN WriteNum(refVersion + 10B);
    ELSE WriteNum(refVersion);
    END;
    WriteRb(ident);
    DumpBytes(SpellingIndex(thisCompileUnit^.name),0);
    WriteRb(ident); (* new feature kjg 1-Apr-89 *)
    DumpBytes(SpellingIndex(callSy),0);
    WriteRb(keySy); WriteNum(symKeyValue);
    WITH thisCompileUnit^.body^ DO
      IF IsEmpty(statements) AND IsEmpty(finalSeq) AND NoMods(nestBlks) THEN
        WriteRb(nilSy);
      END;
    END;
    IF nonRec IN modState THEN WriteRb(bar) END;
  (*
   * write out imports
   *)
    WriteRb(importSy);
    InitCursor(globalModList,curs);
    WHILE NOT Ended(curs) DO
      GetNext(curs,elem);
      (* Assert(elem^.idClass = exportNode); *)
      IF elem^.loaded THEN
	IF NOT elem^.macro AND NOT elem^.system THEN (* usual case *)
          WriteRb(ident); DumpBytes(SpellingIndex(elem^.name),0);
          WriteRb(keySy); WriteNum(elem^.keyValue);
        ELSIF elem^.macro AND (elem^.libSpx <> 0) THEN (* macro with library *)
	  WriteRb(litstring); DumpBytes(elem^.libSpx,0);
	END;
      END;
    END;
    IF exceptOK THEN
      WriteRb(ident); DumpBytes(SpellingIndex(exceptName),0);
      WriteRb(keySy); WriteNum(exceptKey);
    END;
    WriteRb(endSy);
  (*
   * terminate file
   *)
    WriteRb(eofSy);
    CloseRefFile();
  END WriteRefFile;

END M2RefFile.
