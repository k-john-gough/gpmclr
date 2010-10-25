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
(****************************************************************)
(* update record : 11-nov-84, more efficient freelist. kjg      *)
(*		   20-Nov-86, make GetNext() into pure proc     *)
(****************************************************************
$Log: gensequencesupport.mod,v $
Revision 1.1  1996/09/06 07:49:15  lederman
Initial revision

*)

IMPLEMENTATION MODULE GenSequenceSupport; (* K.John Gough 1984 *)

(*$I-*) (*$R-*)

FROM Storage IMPORT ALLOCATE, DEALLOCATE;
FROM SYSTEM IMPORT ADDRESS;

TYPE ElemPtr = POINTER TO Element;
     Element = RECORD
		 child : ADDRESS;
		 next  : ElemPtr
	       END;

VAR  free : ElemPtr;

PROCEDURE GetElement(VAR p : ElemPtr);
BEGIN
  IF free # NIL THEN (* free has a node *)
    p := free;
    free := free^.next
  ELSE
    ALLOCATE(p,SIZE(p^));
  END
END GetElement;

PROCEDURE InitSequence(VAR seq : Sequence);
BEGIN
  WITH seq DO
    first := NIL;
    last  := NIL
  END
END InitSequence;

PROCEDURE LinkLeft(VAR seq : Sequence; element : ADDRESS);
  VAR ptr : ElemPtr;
BEGIN
  GetElement(ptr);
  ptr^.child := element;
  ptr^.next  := seq.first; (* gets NIL if this is first node! *)
  seq.first  := ptr;
  (* now check: is this first child? *)
  IF seq.last = NIL THEN seq.last := ptr END
END LinkLeft;

PROCEDURE LinkRight(VAR seq : Sequence; element : ADDRESS);
  VAR ptr : ElemPtr;
BEGIN
  GetElement(ptr);
  ptr^.child := element;
  ptr^.next  := NIL;
  IF seq.last = NIL THEN (* first child *)
    seq.first := ptr
  ELSE
    seq.last^.next := ptr
  END;
  seq.last := ptr
END LinkRight;

PROCEDURE InitCursor(seq : Sequence; VAR cursor : ElemPtr);
BEGIN
  cursor := seq.first
END InitCursor;

PROCEDURE GetFirst(seq : Sequence;
		   VAR cursor : ElemPtr;
		   VAR result : ADDRESS);
BEGIN
  IF seq.first = NIL THEN result := NIL;
  ELSE
    cursor := seq.first^.next;
    result := seq.first^.child;
  END;
END GetFirst;

PROCEDURE GetNext(VAR cursor : ElemPtr;
		  VAR result : ADDRESS);
BEGIN
  IF cursor = NIL THEN result := NIL;
  ELSE
    result := cursor^.child;
    cursor := cursor^.next;
  END;
END GetNext;

PROCEDURE Ended(cursor : ElemPtr) : BOOLEAN;
BEGIN RETURN (cursor = NIL) END Ended;

PROCEDURE IsEmpty(seq : Sequence) : BOOLEAN;
BEGIN RETURN (seq.first = NIL) END IsEmpty;

PROCEDURE NextIsLast(cursor : ElemPtr) : BOOLEAN;
BEGIN
  RETURN (cursor <> NIL) AND (cursor^.next = NIL)
END NextIsLast;

PROCEDURE LengthOf(seq : Sequence) : CARDINAL;
VAR thisone : ElemPtr;
    index   : CARDINAL;
BEGIN
  thisone := seq.first;
  index := 0;
  WHILE thisone <> NIL DO
    thisone := thisone^.next;
    INC(index)
  END;
  RETURN index
END LengthOf;

PROCEDURE DisposeList(VAR seq : Sequence);
BEGIN
  IF seq.first = NIL THEN RETURN END;
  seq.last^.next := free;
  (* if freelist empty, seq.last^.next = NIL *)
  free := seq.first;
  seq.first := NIL;
  seq.last := NIL
END DisposeList;

BEGIN (* initialise free list *)
  free := NIL
END GenSequenceSupport.
