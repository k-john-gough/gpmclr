(****************************************************************)
(*                                                              *)
(*              Modula-2 Compiler Source Module                 *)
(*                                                              *)
(*        Generation of Unique Names for Bootstrap Version      *)
(*                                                              *)
(*      (c) copyright 1988 Faculty of Information Technology    *)
(*                                                              *)
(*      original module : kjg June 1988                         *)
(*      modifications   : fix for problem of generating linker  *)
(*                        names with dual visibility  28-Jan-89 *)
(*                      : cache names for ind. uplev. 12-Feb-89 *)
(*			: fix bug with type aliases   27-Mar-89 *)
(*			: change entry point name     19-May-89 *)
(*                      : long names for interfaces   13-Dec-90 *)
(*                                                              *)
(****************************************************************
$Log: m2namgen.mod,v $
Revision 1.6  1997/01/16 04:39:27  gough
 new name-munging code which puts new name in the linkName field.

Revision 1.5  1996/01/08 05:29:21  gough
initialise varUseSet for variables

Revision 1.4  1995/09/15 07:45:22  gough
 new procedure MakeNewCurrent creates an "anon" temp in the current
 scope, with the TyNodeClass as specified.

# Revision 1.3  1995/03/14  01:15:18  gough
# CreateCallSmbl gives the smbl a procedure class
#
# Revision 1.2  1995/03/02  08:50:00  gough
# implementation of new procedure MakeTempName
#
# Revision 1.1  1994/04/07  05:03:32  lederman
# Initial revision
#
*****************************************************************)

IMPLEMENTATION MODULE M2NamGenerate;

IMPORT StdError;

FROM M2NodeDefs IMPORT
        IdTree, IdDesc, IdRec, IdNodeClass, FormalClass,
	UsesSet, VarUses, TypeDesc, TypeRec, TyNodeClass, 
        CreateIdDesc, InsertRef, InsertByName,
	CreateTypeDesc, current, thisCompileUnit;
FROM M2TabInitialize IMPORT PointerTo;
FROM M2SSUtilities IMPORT LookupInThisScope;
FROM M2Alphabets IMPORT HashBucketType;
FROM M2NameHandler IMPORT anonBkt, GetSourceRep, StringTable, EnterString;
FROM M2InOut IMPORT ErrIdent, DiagName;
FROM M2MachineConstants IMPORT linkNameLength, lnkSuffixLngth;
FROM ProgArgs IMPORT Assert;

  (* ==================================================== *)
  (* These constants control the linker name conventions. *)
  (* Names are formed by concatenating the identifier     *)
  (* name (truncated to length preLen) and the defining   *)
  (* module name (truncated to length modLen. For example *) 
  (* if preLen = modLen = 3, the linker name generated    *)
  (* for id FoodItem from module BarCode would be FooBar. *)
  (* ==================================================== *)
  CONST totLen = linkNameLength;          (* total length *)
        modLen = lnkSuffixLngth;          (* module part  *)
        preLen = totLen - modLen;         (* prefix part  *)
  (* ==================================================== *)

  VAR tempNam : ARRAY [0 .. 5] OF CHAR;

  PROCEDURE MakeNewCurrent(cls : TyNodeClass;
		       VAR new : IdDesc);
    VAR ok : BOOLEAN;
  BEGIN
    CreateIdDesc(anonBkt,new,varNode);
    new^.varType  := PointerTo(cls);
    new^.varClass := auto;
    new^.varUseSet := UsesSet{defined,directUse};
    MakeTempName(new);
    InsertRef(current^.scope, new, ok);
  END MakeNewCurrent;

  PROCEDURE CreateCallName(isBase : BOOLEAN);
    VAR str   : ARRAY [0 .. 79] OF CHAR;
	ix    : CARDINAL;
	dummy : IdDesc;
	ok    : BOOLEAN;
  BEGIN
    IF isBase THEN str := "Start"; ix := 5;
    ELSE str := "Init"; ix := 4;
    END;
    GetSourceRep(thisCompileUnit^.name,str,ix);
    str[linkNameLength] := 0C;
    EnterString(str,callSmbl);
    CreateIdDesc(callSmbl,dummy,procHeader);
    InsertRef(linkScope,dummy,ok);
    Assert(ok);
  END CreateCallName;

  PROCEDURE MakeTempName(id : IdDesc);
  BEGIN
    INC(tempNam[4]);
    IF tempNam[4] > '9' THEN
      tempNam[4] := '0';
      INC(tempNam[3]);
      IF tempNam[3] > '9' THEN
        tempNam[3] := '0';
        INC(tempNam[2]);
        IF tempNam[2] > '9' THEN
          tempNam[2] := '0';
          INC(tempNam[0]);
	  Assert(tempNam[0] <= 'z', "too many temporaries");
	END;
      END;
    END;
    EnterString(tempNam,id^.name);
  END MakeTempName;

  PROCEDURE MakeNameUnique(VAR scope : IdTree;
                               iPtr  : IdDesc);
    VAR oldHsh, newHsh : HashBucketType;
        str : ARRAY [0..39] OF CHAR;
        ix  : CARDINAL;
        ok  : BOOLEAN;
        ptr : IdDesc;
  BEGIN
    oldHsh := iPtr^.linkName;		(* probably the same as iPtr^.name *)
    LookupInThisScope(scope,oldHsh,ptr);
    IF ptr <> iPtr THEN (* not already present *)
      IF ptr = NIL THEN InsertByName(scope,oldHsh,iPtr,ok);
      (*
	 it is possible that these two are aliases for the
	 same actual type. This possibility must be eliminated
      *)
      ELSIF (iPtr^.idClass <> typeNode) OR
	    (ptr^.idClass <> typeNode) OR
	    (iPtr^.typType <> ptr^.typType) THEN (* name clash *)
        str := "_/0"; ix := 3;
        GetSourceRep(oldHsh,str,ix);
        REPEAT (* change name and retry insert *)
	  IF str[1] <> '9' THEN 
            INC(str[1]);
	  ELSE (* unlikely, but better safe than sorry! *)
	    str[1] := "0"; INC(str[2]);
	  END;
          EnterString(str,newHsh); iPtr^.linkName := newHsh;
          InsertByName(scope,newHsh,iPtr,ok);
        UNTIL ok;
      END; (* if name clash *)
    END; (* if not already present *)
  END MakeNameUnique;

  PROCEDURE MakeLinkerName(iPtr : IdDesc);
    VAR ok       : BOOLEAN;
        ix, idIx : CARDINAL;
        mungName : ARRAY [0..47] OF CHAR;
	newMod   : IdDesc;
        newHsh   : HashBucketType;
        clash    : IdDesc;
  BEGIN
    ix := 0;
    WITH iPtr^ DO
     (*
      *  Here is a fix for the difficulty that arises when an object
      *  is visible both qualified and unqualified: when the qualified
      *  insertion is attempted, the (modified) name is already present.
      *  Note that the qualified object has the modified name already,
      *  since the export tree only has an alias ptr to the unique IdRec.
      *)
      LookupInThisScope(linkScope,linkName,clash); (* usually clash = NIL *)
      IF clash <> iPtr THEN (* not already present, so ... *)
        IF idClass = varNode THEN (* assert this is not a param *)
          IF origMod = NIL THEN newMod := thisCompileUnit;
          ELSE newMod := origMod;
          END;
        ELSIF idClass = externProc THEN newMod := module;
        ELSIF idClass = procHeader THEN newMod := thisCompileUnit;
        ELSE Assert(FALSE);
        END;
        (*
         *  if newMod = thisCompileUnit then the field
         *  "direct" is not in the active variant ...
         *  idClass = modNode is an equiv test
         *)
        IF (newMod^.idClass = modNode) OR
            NOT newMod^.direct THEN
          GetSourceRep(newMod^.name,mungName,ix);
          IF ix > modLen THEN ix := modLen END;
	  mungName[ix] := "_"; INC(ix);
	  idIx := ix;
          GetSourceRep(name,mungName,ix);
          IF ix > idIx + preLen THEN
            ix := idIx + preLen;
            mungName[ix] := 0C;
	  END;
          EnterString(mungName,newHsh);
	  linkName := newHsh;
        ELSIF newMod^.direct THEN
         (* ========================================================= *)
         (* ====== optional aliases in interface symbol files ======= *)
         (* ========================================================= *)
          IF (idClass = varNode) THEN
            idIx := varOffset;
          ELSIF (idClass = externProc) THEN
            idIx := extAlias;
          END;
          IF idIx <> 0 THEN
            ix := 0;
            REPEAT
              mungName[ix] := StringTable(idIx + ix);
              INC(ix)
            UNTIL mungName[ix - 1] = "";
            EnterString(mungName,newHsh);
            linkName := newHsh;
          END;
         (* ========================================================= *)
	END; (* else name already is final *)
        InsertByName(linkScope,linkName,iPtr,ok);
        IF NOT ok THEN ErrIdent(302,name) END;
      END; (* if not already present *)
    END; (* with *)
  END MakeLinkerName;

BEGIN
  linkScope := NIL;
  tempNam   := "a$000";
END M2NamGenerate.
