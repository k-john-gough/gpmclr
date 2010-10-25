(****************************************************************)
(*                                                              *)
(*              Modula-2 Compiler Source Module                 *)
(*                                                              *)
(*               Tree to Tree Transformations                   *)
(*                                                              *)
(*      (c) copyright 1988 Faculty of Information Technology    *)
(*                                                              *)
(*      original module : kjg May 1988                          *)
(*      modifications   : 19-Sep-88 fix propagate procedure     *)
(*			: 18-Apr-89 fix uplevel module imports  *)
(*			:  1-Nov-89 lazy parameter evaluation   *)
(*			: 27-Feb-90 externProcs now on adjBlk	*)
(*			: 30-Aug-90 fix call to MkLk for stProc *)
(*			: 23-Jan-91 insert indirect mods in scp *)
(*                                                              *)
(****************************************************************)
(*              MODIFIED FOR NATIVE CODE VERSIONS               *)
(****************************************************************
*****************************************************************)

IMPLEMENTATION MODULE M2TreeToTree;

IMPORT InOut;

  FROM GenSequenceSupport IMPORT
        Sequence, IsEmpty, Ended, ElemPtr, InitCursor,
        InitSequence, LinkRight, DisposeList, GetFirst, GetNext;

  FROM M2NodeDefs IMPORT
	current, IdString, codeBlkList,
        IdTree, TreeRec, FormalClass,
        IdDesc, IdRec, IdNodeClass,
        TypeDesc, TypeRec, TyNodeClass,
        StrucTree, StrucRec, InsertRef,
        FormalType, FormalRec, globalModList,
        Attribute, AttributeSet,
        modState, infinity,
        thisCompileUnit;

  FROM M2NamGenerate IMPORT
        CreateCallName, MakeNameUnique, MakeLinkerName, linkScope;

  FROM M2Alphabets   IMPORT
        HashBucketType, ModStateFlags, ModStateSet;

  FROM M2InOut       IMPORT ErrIdent, Error, lastPos, DiagName;
  FROM M2SSUtilities IMPORT LookupInThisScope;
  FROM M2NameHandler IMPORT EnterString, anonBkt;
  FROM M2SetTemporaries IMPORT MarkSetExpressions;

  (******************************************************)

  PROCEDURE FlattenProcs();
  (* this procedure performs  TWO  tasks: (i) M2Traversal has   *)
  (* already included module bodies inline at the start of the  *)
  (* enclosing block, and the variable name-spaces must now be  *)
  (* merged; (ii) the procedure and function name spaces must   *)
  (* be flattened by changing procedure names if necessary, and *)

    PROCEDURE MoveObjects(sScp : IdTree;  (* the source scope tree *)
			  dFrm : IdDesc); (* the destination frame *)
      (* this procedure moves the variables and types of  *)
      (* a nested module to the immediately outside scope *)
      (* note that correctness depends on multiply nested *)
      (* scopes appearing on the list in inside-out order *)
      (* The second line of the IF excludes imported vars *)
      (* from uplevel frames from being considered local  *)
    BEGIN (* pre-order walk *)
      IF sScp <> NIL THEN
        WITH sScp^ DO
          IF (ident^.idClass = varNode) AND
	     (ident^.decFrame = dFrm) THEN
            MakeNameUnique(dFrm^.scope,ident);
          END;
          MoveObjects(left,dFrm); MoveObjects(right,dFrm);
        END;
      END;
    END MoveObjects;

    VAR ix : INTEGER;
	id : IdDesc;
  BEGIN
    FOR ix := 0 TO HIGH(codeBlkList) DO
      id := codeBlkList[ix];
      WITH id^ DO
	MarkSetExpressions(id);
	IF idClass = procNode THEN
	  IF  uphill <> thisCompileUnit THEN
            MakeNameUnique(thisCompileUnit^.scope, id);
          END;
	ELSIF idClass = modNode THEN
	  (* M2Traverse did inline, must now fix scope *)
	  MoveObjects(scope,frame);
        END;
      END; 
    END;
    MarkSetExpressions(thisCompileUnit);
  END FlattenProcs;

  PROCEDURE CreateLinkNames();
  (* this procedure transforms all external names into   *)
  (* the form known to the linker. The new scope has C   *)
  (* reserved words already excluded                     *)

    VAR  qualTrees : Sequence; (* of exportNode IdDescs *)

    PROCEDURE MakeQualsGlobal();
      (* this procedure takes export node trees in the   *)
      (* global scope and moves type, procedure and var  *)
      (* names to the global scope. For procs and vars   *)
      (* the linker names are constructed also           *)

      VAR qCrs : ElemPtr; mod : IdDesc;


      PROCEDURE Flatten(tree : IdTree);
      BEGIN
        IF tree <> NIL THEN
          WITH tree^ DO
            CASE ident^.idClass OF
            | varNode : MakeLinkerName(ident); 
	        ident := NIL;
            | externProc : 
		MakeLinkerName(ident); 
		ident := NIL;
            | conProc : 
	        MakeLinkerName(ident^.procId);
		ident := NIL;
            ELSE (* nothing *)
            END; (* case *)
            Flatten(left); Flatten(right);
          END; (* with *)
        END; (* if *)
      END Flatten;

    BEGIN
      InitCursor(qualTrees,qCrs);
      WHILE NOT Ended(qCrs) DO
        GetNext(qCrs,mod);
        Flatten(mod^.exports);
(*
 *    flattened names may already be in the linker scope if
 *   objects are visible both directly and in qualified mode
 *)
      END;
      DisposeList(qualTrees);
    END MakeQualsGlobal;

    PROCEDURE LinkNames(src : IdTree);
      VAR class : IdNodeClass;
    BEGIN
      IF src <> NIL THEN
        WITH src^ DO
          CASE ident^.idClass OF
            varNode :
              IF  (ident^.varClass = export) OR
                  (ident^.varClass = extern) THEN
                MakeLinkerName(ident); 
		(* ident := NIL; *)
	      ELSE MakeNameUnique(linkScope,ident);
              END;
          | procHeader, externProc :
              MakeLinkerName(ident); 
	      (* ident := NIL; *)
	  | conProc :
	      class := ident^.procId^.idClass;
	      IF (class = procNode) OR
		 (class = stProc)   OR
		 (class = stFunc)   THEN (* skip *)
	      ELSE (* procHeader or externProc *)
	        MakeLinkerName(ident^.procId);
	        (* ident := NIL; *)
	      END;
          | exportNode : LinkRight(qualTrees,ident);
          ELSE (* nothing *)
          END;
          LinkNames(left); LinkNames(right);
        END;
      END;
    END LinkNames;

  BEGIN
    CreateCallName(progMod IN modState);
    InitSequence(qualTrees);
    LinkNames(thisCompileUnit^.scope);
    MakeQualsGlobal();
  END CreateLinkNames;

  PROCEDURE TransformTree;
  BEGIN
   (*
    *  ALL error messages now go to body^.headerLine...
    *  lastPos.line := thisCompileUnit^.body^.visitDepth;
    *)
    lastPos.line := thisCompileUnit^.body^.headerLine;
    FlattenProcs(); (* & expand init calls inline  *)
    (* any other inline expansions will go here... *)
    CreateLinkNames(); (* and flatten qual scopes  *)
    (* now finally, make the linkScope the global scope *)
    thisCompileUnit^.scope := linkScope;
  END TransformTree;

END M2TreeToTree.
