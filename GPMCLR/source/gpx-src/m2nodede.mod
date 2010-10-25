(****************************************************************)
(*								*)
(*		Modula-2 Compiler Source Module			*)
(*								*)
(*                   Syntax Tree Node Definitions               *)
(*								*)
(*    (c) copyright 1988 Faculty of Information Technology      *)
(*								*)
(*      original module : Feb 1988 (M2Comp.idl @ 21-Feb-88)     *)
(*      modifications   : 29-Mar-88 import/export lists         *)
(*			: 22-May-89 init type size & alignment  *)
(*			: 27-May-89 insert with uplevel check   *)
(*			: 02-Oct-89 default size of type is 1   *)
(*			: 07-Nov-89 some alignMasks set here	*)
(*			: 13-Jul-90 Insert's set-like semantics *)
(*			: 14-Aug-91 initialize anonTypes seq	*)
(*			: 12-Apr-92 jrh fwdMod idClass added    *)
(*			:               fwdTargets for unknown	*)
(*								*)
(****************************************************************
$Log: m2nodede.mod,v $
Revision 1.8  1997/01/16 04:43:27  gough
        new procedure InsertByName, which inserts an IdDesc into a
        scope based on the given hashBucketNumber, rather than the
        name of the IdDesc.  New IdDesc type posParNode, new field
        linkName.  MakeFormal takes another parameter, the typeName.

Revision 1.7  1996/11/27 02:14:31  lederman
add init for normalRef and codeBlkList

Revision 1.6  1996/07/30 00:08:48  gough
initialize type-descriptors of stringTs class

Revision 1.5  1996/01/08 05:30:12  gough
initialise new fields

# Revision 1.4  1995/03/23  22:59:19  gough
# initialize new field od == number of open dimensions in FormalType
#
# Revision 1.3  1994/11/15  04:33:30  gough
#  new field origNam in IdRec, remove cshIndex field
#
# Revision 1.2  1994/07/01  04:55:51  lederman
# make alignment variable on bytesInWord
#
# Revision 1.1  1994/04/07  05:06:03  lederman
# Initial revision
#
*****************************************************************)

IMPLEMENTATION MODULE M2NodeDefs;

FROM SYSTEM IMPORT TSIZE, CAST;

FROM M2Alphabets IMPORT Spellix, HashBucketType, LexAttType,
                        ModStateFlags, ModStateSet;
FROM GenSequenceSupport IMPORT Sequence, LinkRight, InitSequence;
FROM M2MachineConstants IMPORT adrSize, bytesInWord;
FROM M2NameHandler IMPORT anonBkt, CheckUsed;
FROM M2InOut IMPORT Error, ErrIdent, DiagName;
FROM StdError IMPORT Write, WriteString, WriteCard;
FROM Storage IMPORT ALLOCATE, DEALLOCATE;
FROM ProgArgs IMPORT Assert;

(* FROM Terminal IMPORT WriteString, WriteCard, WriteLn; *)
(*
 *  VAR globalModList   : Sequence;
 *      thisCompileUnit : IdDesc;
 *      pervasiveUnit   : IdDesc;
 *      unitImports, unitExports : Sequence; (* of IdDesc *)
 *	current         : IdDesc;
 *	lexLevel	: [0 .. 16];
 *)

    VAR inserting : BOOLEAN;
        suspended : BOOLEAN;

    PROCEDURE SuspendList();
    BEGIN
      suspended := inserting;
      inserting := FALSE;
    END SuspendList;

    PROCEDURE ResumeList();
    BEGIN inserting := suspended END ResumeList;

    PROCEDURE StartImportList();
    BEGIN (* uses export list as surrogate *)
      inserting := TRUE;
    END StartImportList;

    PROCEDURE StartExportList();
    BEGIN (* copy previous list, then start again *)
      Assert(thisCompileUnit^.idClass = modNode);
      unitImports := unitExports;
      InitSequence(unitExports);
    END StartExportList;

    PROCEDURE MakeTree(id : IdDesc) : IdTree;
      VAR ptr : IdTree;
    BEGIN
      ALLOCATE(ptr,TSIZE(TreeRec));
      WITH ptr^ DO
          left  := NIL; right := NIL;
          name  := id^.name; ident := id;
      END;
      RETURN ptr;
    END MakeTree;
 
    PROCEDURE InsertAndCheck(VAR sc : IdRec;
                                 id : IdDesc;
                             VAR ok : BOOLEAN);
    (* precondition  : sc is a valid proc or mod descriptor  *)
    (* postcondition : id is inserted in tree                *)

        VAR ptr : IdTree; key : HashBucketType;

    BEGIN
      key := id^.name; ok := TRUE;
      IF sc.scope = NIL THEN (* first node in tree *)
	sc.scope := MakeTree(id);
      ELSE (* search for correct position *)
	ptr := sc.scope;
        LOOP
          WITH ptr^ DO
            IF key < name THEN
              IF left = NIL THEN
		left := MakeTree(id); EXIT;
              ELSE ptr := left;
              END;
            ELSIF key > name THEN
              IF right = NIL THEN
		right := MakeTree(id); EXIT;
              ELSE ptr := right;
              END;
            ELSIF ident = id THEN EXIT; (* set-like semantics *)
	    (* exit with success if node is already present *)
            ELSE ok := FALSE; EXIT;
            END; (* if key ... *)
          END; (* with *)
        END (* loop *)
      END; (* if nil *)
      IF ok AND CheckUsed(sc.body^.usedBkts,key) THEN ErrIdent(308,key) END;
      IF inserting AND ok AND (sc.scope = current^.scope) THEN
        LinkRight(unitExports,id);
      END;
    END InsertAndCheck;

    PROCEDURE InsertRef(VAR t : IdTree;
                           id : IdDesc;
                       VAR ok : BOOLEAN);
    (* precondition  : t is a valid tree (possibly empty)    *)
    (* postcondition : id is inserted in tree                *)

        VAR ptr : IdTree; key : HashBucketType;

    BEGIN
      key := id^.name; 
      ok := TRUE;
      IF t = NIL THEN (* first node in tree *)
	t := MakeTree(id);
      ELSE (* search for correct position *)
        ptr := t;
        LOOP
          WITH ptr^ DO
            IF key < name THEN
              IF left = NIL THEN
		left := MakeTree(id); EXIT;
              ELSE ptr := left;
              END;
            ELSIF key > name THEN
              IF right = NIL THEN
		right := MakeTree(id); EXIT;
              ELSE ptr := right;
              END;
            ELSIF ident = id THEN EXIT; (* set-like semantics *)
	    (* exit with success if node is already present *)
            ELSE ok := FALSE; EXIT;
            END; (* if key ... *)
          END; (* with *)
        END (* loop *)
      END; (* if nil *)
      IF inserting AND ok AND (t = current^.scope) THEN
        LinkRight(unitExports,id);
      END;
    END InsertRef;

    PROCEDURE InsertByName(VAR tree : IdTree;
			       hash : HashBucketType;
                               idnt : IdDesc;
                           VAR ok   : BOOLEAN);
      VAR ptr : IdTree;
    BEGIN
      ok := TRUE;
      IF tree = NIL THEN (* first node in tree *)
	tree := MakeTree(idnt); tree^.name := hash;
      ELSE (* search for correct position *)
        ptr := tree;
        LOOP
          WITH ptr^ DO
            IF hash < name THEN
              IF left = NIL THEN
		left := MakeTree(idnt); left^.name := hash; EXIT;
              ELSE ptr := left;
              END;
            ELSIF hash > name THEN
              IF right = NIL THEN
		right := MakeTree(idnt); right^.name := hash; EXIT;
              ELSE ptr := right;
              END;
            ELSIF ident = idnt THEN EXIT; (* set-like semantics *)
	    (* exit with success if node is already present *)
            ELSE ok := FALSE; EXIT;
            END; (* if hash ... *)
          END; (* with *)
        END (* loop *)
      END; (* if nil *)
    END InsertByName;

    (* ----------------------------------------------------- *)

    PROCEDURE CreateIdDesc(nam : HashBucketType;
                       VAR ptr : IdDesc;
                           tag : IdNodeClass);
    (* postcondition : space is allocated, and idClass is set.
                       *Type is set to NIL. In the case of 
                       procs, funcs mods and exports, scope
                       pointers are set to zero as well.     *)
    BEGIN
      ALLOCATE(ptr,TSIZE(IdRec)); (* IdRecSize[tag] ? *)
      WITH ptr^ DO
        name     := nam;
        linkName := nam;
        idClass  := tag;
        clrName  := anonBkt;
        CASE tag OF
        | constNode  : conType   := NIL;
        | typeNode   : typType   := NIL;
	| conProc    : procId    := NIL;
        | varNode    :
            varType := NIL;
            origMod := NIL;
	    enclFrm := current;
	    decFrame := current^.frame;
	    lexLev   := lexLevel;
	    varUseSet := UsesSet{};
	    normalRef := FALSE;
	    hiDepth   := 0;
        | fieldNode  :
            fieldType := NIL;
            unionSpx  := 0; (* ==> no union prefix *)
        | exportNode : 
            exports  := NIL;
            loaded   := FALSE;
            system   := FALSE;
            library  := FALSE;
            macro    := FALSE;
            direct   := FALSE;
            retCut   := FALSE;
            keyValue := 0; (* the empty key *)
        | procHeader, procNode, modNode, fwdHeader, fwdMod :
            scope   := NIL;
            uphill  := NIL;
            body    := NIL;
            outside := NIL;
	    (* frame must be set explicitly *)
        | externProc : 
	    nonLeaky := FALSE;
	| unknown :
	    InitSequence(fwdTargets);
        ELSE (* no init. *)
        END;
      END;
    END CreateIdDesc;

    (* ----------------------------------------------------- *)

    PROCEDURE CreateTypeDesc(modDes : IdDesc;
                            VAR ptr : TypeDesc;
                                tag : TyNodeClass);
    (* postcondition : desc. is allocated, tyClass is set    *)
      VAR   mask     : CHAR;
	    tSiz     : CARDINAL;
    BEGIN
      (*   7-Nov-89 (kjg) 
	 the following types have size initialized
	   enums, hiddens, opaques, pointers, procs, others get "0"
	 the following types have alignment initialized
	   enums, hiddens, opaques, pointers, procs, sets
      *)
      mask := 0C; tSiz := 0;
      ALLOCATE(ptr,TSIZE(TypeRec));
      WITH ptr^ DO
        tyName  := anonBkt;
	tyNumber := 0;
        parentMod := modDes;
        dumped  := FALSE;
        pubTag  := notPub;
        listed  := FALSE;
        tyClass := tag;
        CASE tyClass OF
        | subranges : hostType    := NIL;
	| hiddens   : tSiz := adrSize; mask := CHR(bytesInWord - 1);
        | unions    : InitSequence(varSeq);
        | enums     : InitSequence(conSeq); tSiz := 1;
        | sets      : baseType    := NIL; 
		      mask := CHR(bytesInWord - 1);
        | pointers, stringTs : 
		      targetType  := NIL; 
		      tSiz := adrSize; mask := CHR(bytesInWord - 1);
        | arrays    : elementType := NIL;
                      indexType   := NIL;
                      isDynamic   := FALSE;
        | records :   InitSequence(fieldSeq);
            	      fields := NIL;
        | procTypes, funcTypes :
	              InitSequence(params);
	              result := NIL; 
		      tSiz := adrSize; 
		      mask := CHR(bytesInWord - 1);
		      parSiz := infinity;
		      preCon := NIL;
	| opaqueTemp: resolvedType := NIL; 
		      tSiz := adrSize; mask := CHR(bytesInWord - 1);
        ELSE (* no init *)
        END; (* case *)
	size := tSiz; alignMask := mask;
      END; (* with *)
    END CreateTypeDesc;

    (* ----------------------------------------------------- *)

    PROCEDURE MakeFormal(tp : TypeDesc;
                         fn : HashBucketType;
			 tn : HashBucketType;
                         fc : FormalClass;
			 od : CARDINAL) : FormalType;
      VAR ptr : FormalType;
    BEGIN
      ALLOCATE(ptr,TSIZE(FormalRec));
      WITH ptr^ DO
        type := tp;
        fNam := fn;
        tNam := tn;
        form := fc;
        dimN := od;
        Assert(od <= 64, "Open array dimensions > 64");
      END;
      RETURN ptr
    END MakeFormal;

BEGIN
  thisCompileUnit := NIL; symKeyValue := 0;
  current := NIL; 
  lexLevel := 0;
  inserting := FALSE;
  InitSequence(globalModList);
  InitSequence(unitImports);
  InitSequence(unitExports);
  NEW(codeBlkList, 4);
  modState := ModStateSet{objectCode,peepOpt .. argOpt};
END M2NodeDefs.
