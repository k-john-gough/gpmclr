(****************************************************************)
(*								*)
(*		Modula-2 Compiler Source Module			*)
(*								*)
(*               More Syntax Tree Node Definitions              *)
(*								*)
(*    (c) copyright 1988 Faculty of Information Technology      *)
(*								*)
(*      original module : April 1988, jh & kjg                  *)
(*      modifications   : 27-Feb 89 explicit emptyNode          *)
(*      last modified   : 17-Feb 91 line number of emptyNode    *)
(*								*)
(****************************************************************
$Log: m2struct.mod,v $
Revision 1.6  1997/01/16 05:11:01  gough
all new stuff for case statments.

Revision 1.5  1996/11/27 02:59:03  lederman
init exceptSeq, finalSeq, finalExSeq and exceptDesc fields

Revision 1.4  1995/09/15 08:00:20  gough
initialize new field for for-statement descriptor

Revision 1.3  1995/03/14 01:54:13  gough
Initialize new fields in the body attribute structure

# Revision 1.2  1994/07/05  05:01:00  lederman
# make maxParSize vary with bytesInWord
#
# Revision 1.1  1994/04/07  05:23:54  lederman
# Initial revision
#
*****************************************************************)

IMPLEMENTATION MODULE M2StructureDefs;

FROM SYSTEM IMPORT TSIZE; (* obsolete syntax for LogiTech *)
FROM M2NodeDefs IMPORT IdDesc, TypeDesc, TyNodeClass,
        Attribute, AttributeSet,
        StrucRec, StrucTree, IdNodeClass;
FROM M2Designators IMPORT DesigRec, WithDesc,
        InitDesignator, WithRec, ExprDesc;
FROM M2Alphabets IMPORT LexAttType, HashBucketType,
        Flags, FlagSet;
FROM M2NameHandler IMPORT UsedSetPtr, InitUsed;
FROM M2MachineConstants IMPORT bytesInWord;
FROM M2Scanner IMPORT CurrentFlags;
FROM M2InOut IMPORT lastPos, Position;
FROM GenSequenceSupport IMPORT Sequence, InitSequence, LinkLeft;
FROM Storage IMPORT ALLOCATE;


  VAR nextLoopLabel : CARDINAL;
      empty         : StatDesc; (* an empty statment *)

  PROCEDURE CreateStrucTree(VAR block : IdDesc);
  (* postcondition : StrucTree is allocated and initialized *)
    VAR temp : StrucTree;
  BEGIN
    ALLOCATE(temp, TSIZE(StrucRec));
(*
    ALLOCATE(block^.body,TSIZE(StrucRec));
    WITH block^.body^ DO
 *)
    NEW(temp^.nestBlks, 4);
    WITH temp^ DO
      InitSequence(adjustSeq);
      InitSequence(statements);
      InitSequence(exceptSeq);
      InitSequence(finalSeq);
      InitSequence(finalExSeq);
      exceptDesc := NIL;
      callAttrib := AttributeSet{};
      IF fastCode IN CurrentFlags() THEN
        INCL(callAttrib,optimize);
      END;
      IF stackTests IN CurrentFlags() THEN
        INCL(callAttrib,stackCheck);
      END;
      InitUsed(usedBkts);
      visitDepth := 0;
      tempSize   := 0;
      maxParSize := 4 * bytesInWord;
      headerLine := lastPos.line;
      loopJunk := NIL;
(*
      NEW(nestBlks,4);
 *)
    END;
    block^.body := temp;
  END CreateStrucTree;

(* ----------------------------------------------------- *)

  PROCEDURE CreateStatDesc(VAR ptr : StatDesc;
                               tag : StatNodeClass);
  BEGIN
    ALLOCATE(ptr,TSIZE(StatRec));
    WITH ptr^ DO
      statClass := tag;
      sourceLoc := lastPos;
      CASE tag OF
      | assignNode, procCallNode, initCallNode :
          InitDesignator(designator);
          InitSequence(actualParams); (* also sets exp. to NIL ! *)
      | caseNode :
          ALLOCATE(caseInfo,TSIZE(CaseStatRec));
          caseInfo^.switch := NIL;
	  NEW(caseInfo^.caseStr,10);
	  NEW(caseInfo^.partStr,4);
          InitSequence(cases);
          InitSequence(default); LinkLeft(default,empty);
      | ifNode       : InitSequence(branches);
      | compoundNode : InitSequence(inlineBody);
      | whileNode, repeatNode : InitSequence(wrBody);
      | loopNode :
          InitSequence(loopBody);
          loopLabel  := nextLoopLabel; INC(nextLoopLabel);
          loopExited := FALSE;
      | forNode :
          InitSequence(forBody);
          stepSize := 1;
          countDownVar := NIL;
      | withNode :
          ALLOCATE(withInfo,TSIZE(WithRec));
          InitDesignator(withInfo^.desig);
          InitSequence(withBody);
      | returnNode : returnResult := NIL;
      | exitNode, emptyNode, retryNode : (* nothing *)
      (* others only arise from transformations *)
      END; (* case *)
    END; (* with *)
  END CreateStatDesc;


  PROCEDURE MakeRangeDesc(left, right : ExprDesc) : RangeDesc;
    VAR ptr : RangeDesc;
  BEGIN
    ALLOCATE(ptr,TSIZE(RangeRec));
    WITH ptr^ DO
      lower := left;
      upper := right;
    END;
    RETURN ptr;
  END MakeRangeDesc;

(* ----------------------------------------------------- *)

  PROCEDURE CreateConditional(VAR ptr : IfDesc);
  BEGIN
    ALLOCATE(ptr,TSIZE(IfRec));
    ptr^.condition := NIL;
    InitSequence(ptr^.statSeq);
  END CreateConditional;

(* ----------------------------------------------------- *)

  PROCEDURE CreateCaseDesc(VAR ptr : CaseDesc);
  BEGIN
    ALLOCATE(ptr,TSIZE(CaseRec));
    InitSequence(ptr^.selRnges);
    InitSequence(ptr^.statSeq);
  END CreateCaseDesc;

(* ----------------------------------------------------- *)

BEGIN
  ALLOCATE(empty,TSIZE(StatRec));
  empty^.statClass := emptyNode;
  empty^.sourceLoc.line := 0;	(* to stop cc complaining *)
  empty^.sourceLoc.pos := 0;	(* to stop cc complaining *)
  nextLoopLabel := 0;
END M2StructureDefs.
