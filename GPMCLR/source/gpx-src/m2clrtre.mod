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
(*			:    Jun-03 CLR version, semantics <>   *)
(*                                                              *)
(****************************************************************)
(*              MODIFIED FOR NATIVE CODE VERSIONS               *)
(****************************************************************)

IMPLEMENTATION MODULE M2ClrTreeToTree;

IMPORT InOut;

  FROM VARSTRS IMPORT APPEND;
  FROM Storage IMPORT ALLOCATE, DEALLOCATE;

  FROM M2NodeDefs IMPORT
	IdString, codeBlkList, IdDesc, IdRec, IdNodeClass, thisCompileUnit;

  FROM M2InOut       IMPORT lastPos;
  FROM M2SetTemporaries IMPORT MarkSetExpressions;

  (*********************************************************)
  (* In Modula-2 procedures that are defined within nested *)
  (* modules are able to be exported from the file level.  *)
  (* FlattenProcs takes any such definitions and appends   *)
  (* them to the nestBlk list of the outer mod-descriptor. *)
  (* The procedure recurses over the nested modules.       *)
  (*********************************************************)

  PROCEDURE FlattenProcs(dst : IdDesc;  (* File-level mod. *)
                         mod : IdDesc); (* Mod. to process *)

    VAR indx : INTEGER;
        elem : IdDesc;
        iLst : IdString;
        dLst : IdString;
        nLst : IdString;
  BEGIN
   (*
    *   Copy the exported procs to the global scope dst.
    *   Build new list in IdDesc^.body of NON-exported procs.
    *)
    iLst := mod^.body^.nestBlks;
    dLst := dst^.body^.nestBlks;
    (* create new scratch list *)
    NEW(nLst, HIGH(iLst) + 1);
    FOR indx := 0 TO HIGH(iLst) DO
      elem := iLst[indx];
      WITH elem^ DO
        CASE idClass OF
        | procNode   : APPEND(nLst, elem);
        | procHeader : APPEND(dLst, elem);
        | modNode    : APPEND(nLst, elem); FlattenProcs(dst, elem);
        END;
      END; 
    END;
    mod^.body^.nestBlks := nLst;
  END FlattenProcs;


  PROCEDURE TransformTree;
    VAR indx : INTEGER;
        iLst : IdString;
        elem : IdDesc;
  BEGIN
   (*
    *    ALL error messages now go to body^.headerLine...
    *)
    lastPos.line := thisCompileUnit^.body^.headerLine;
   (*
    *    Fix the set temporaries as local vars.
    *    ... In native code versions of GPM the size of
    *    the stack frame is computed by the front-end.
    *    This necessitates the allocation of the (possibly
    *    large) set temporaries in the front-end. The back
    *    ends may allocate additional space for scalar temps.
    *    For the CLR the JIT compiler determines the stack
    *    frame size, so this traversal simply names any 
    *    needed temporaries as additional local variables.
    *)
    FOR indx := 0 TO HIGH(codeBlkList) DO
      elem := codeBlkList[indx];
      MarkSetExpressions(elem);
    END;
    MarkSetExpressions(thisCompileUnit);
   (*
    *   Now move exported procs to outer namespace.
    *)
    iLst := thisCompileUnit^.body^.nestBlks;
    FOR indx := 0 TO HIGH(iLst) DO
      elem := iLst[indx];
      IF elem^.idClass = modNode THEN 
        FlattenProcs(thisCompileUnit, elem); 
      END;
    END;
  END TransformTree;

END M2ClrTreeToTree.
