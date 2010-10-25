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
(****************************************************************
$Log: cardtrees.mod,v $
Revision 1.1  1996/09/06 07:49:13  lederman
Initial revision

*)

IMPLEMENTATION MODULE CardTrees;
FROM CardSequences IMPORT Sequence, InitSequence, LinkRight;
FROM Storage IMPORT ALLOCATE, DEALLOCATE;

  TYPE Tree = POINTER TO TreeBlock;
       TreeBlock = RECORD
                     key : CARDINAL;
                     left, right : Tree;
                   END;

  PROCEDURE InitTree(VAR tre : Tree);
  (* postcondition : tre is an empty tree *)
  BEGIN
    tre := NIL;
  END InitTree;

  PROCEDURE IsEmpty(tre : Tree) : BOOLEAN;
  (* postcondition : returns "tre is the empty Tree" *)
  BEGIN
    RETURN tre = NIL;
  END IsEmpty;

  PROCEDURE Insert(VAR tre : Tree; element : CARDINAL);
  BEGIN
    IF tre = NIL THEN
      ALLOCATE(tre,SIZE(tre^));
      WITH tre^ DO
        key := element; left := NIL; right := NIL;
      END;
    ELSIF element < tre^.key THEN Insert(tre^.left,element);
    ELSIF element > tre^.key THEN Insert(tre^.right,element);
    (* else already present *)
    END;
  END Insert;

  PROCEDURE Delete(VAR tre : Tree; element : CARDINAL);
    VAR remKey : CARDINAL; (* largest key in left subtree  *)
        savedTree : Tree;  (* subtree of the disposed node *)

    PROCEDURE RemoveLargest(VAR t : Tree);
      VAR saved : Tree;
    BEGIN (* assert: t <> NIL *)
      IF t^.right <> NIL THEN RemoveLargest(t^.right);
      ELSE (* t^ is it! *)
        remKey := t^.key; (* the removed key *)
        saved := t^.left;
        DEALLOCATE(t,SIZE(t^));
        t := saved;
      END;
    END RemoveLargest;

  BEGIN
    IF tre = NIL THEN RETURN END;
    IF    element < tre^.key THEN Delete(tre^.left,element);
    ELSIF element > tre^.key THEN Delete(tre^.right,element);
    ELSE (* element found, do special cases first *)
      IF tre^.left = NIL THEN
        savedTree := tre^.right;
        DEALLOCATE(tre,SIZE(tre^));
        tre := savedTree;
      ELSIF tre^.right = NIL THEN
        savedTree := tre^.left;
        DEALLOCATE(tre,SIZE(tre^));
        tre := savedTree;
      ELSE (* find and remove largest in left subtree *)
        RemoveLargest(tre^.left);
        tre^.key := remKey; (* copy to deleted node *)
      END;        
    END;
  END Delete;

  PROCEDURE Lookup(tre : Tree; element : CARDINAL) : BOOLEAN;
  BEGIN (* recursive version *)
    IF tre = NIL THEN RETURN FALSE
    ELSIF element < tre^.key THEN RETURN Lookup(tre^.left,element);
    ELSIF element > tre^.key THEN RETURN Lookup(tre^.right,element);
    ELSE RETURN TRUE;
    END;
  END Lookup;
(*
  PROCEDURE Lookup(tre : Tree; element : CARDINAL) : BOOLEAN;
    VAR temp : Tree;
  BEGIN (* iterative version *)
    temp := tre;
    WHILE temp <> NIL DO
      IF    element < temp^.key THEN temp := temp^.left;
      ELSIF element > temp^.key THEN temp := temp^.right;
      ELSE  (* found *) RETURN TRUE;
      END;
    END;
    RETURN FALSE;
  END Lookup;
*)
  PROCEDURE MakeSequence(tre : Tree; VAR seq : Sequence);
    PROCEDURE Link(t : Tree; VAR sq : Sequence);
    BEGIN (* preorder walk *)
      IF t <> NIL THEN
        Link(t^.left,sq);
        LinkRight(sq,t^.key);
        Link(t^.right,sq);
      END;
    END Link;
  BEGIN
    InitSequence(seq);
    Link(tre,seq);    
  END MakeSequence;

END CardTrees.


