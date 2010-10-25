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
(* modification record ---------------------------------------- *)
(*			08-May-92 jrh Arg4 ALLOCATE...+8 not +6	*)
(*                      17-Jan-95 pms INCADR -> ADDADR          *)
(****************************************************************
$Log: buildargs.mod,v $
Revision 1.1  1996/09/06 07:49:10  lederman
Initial revision

*)

IMPLEMENTATION MODULE BuildArgs;

  FROM Ascii IMPORT nul;
  FROM Storage IMPORT ALLOCATE, DEALLOCATE;
  FROM SYSTEM  IMPORT ADR, CAST, ADDADR;
  FROM ProgArgs IMPORT Assert;

  CONST dummy  = 1023;

  TYPE CharPtr = POINTER TO CHAR;

  TYPE ArgPtr  = POINTER TO ARRAY [0 .. dummy] OF CharPtr;
       (* actually UNIX' "typedef char * ArgDef[];" *)
       (* variably sized dynamic arrays of CharPtr  *)

  TYPE BufPtr  = POINTER TO ARRAY [0 .. dummy] OF POINTER TO
                  RECORD
                    high : CARDINAL;
                    chrs : ARRAY [0 .. dummy] OF CHAR;
                  END;

  TYPE ArgBlock = POINTER TO ArgControlBlock;
       ArgControlBlock =
                  RECORD
                    max, next   : CARDINAL;
                    args : ArgPtr;
                    strs : BufPtr;
                  END;
  (* $I- *) (* $R- *)

  PROCEDURE Arg1(a1 : ARRAY OF CHAR) : ArgPtr;
    VAR ptr : ArgPtr; cPtr : CharPtr; ix : CARDINAL;
  BEGIN (* size is 2*ptrs + string-copy *)
    ALLOCATE(ptr,2 * SIZE(CharPtr) + HIGH(a1) + 2);
    cPtr := CAST(CharPtr,ADR(ptr^[2]));
    ptr^[0] := cPtr;
    FOR ix := 0 TO HIGH(a1) DO
      cPtr^ := a1[ix]; cPtr := ADDADR(cPtr,1);
    END;
    cPtr^ := nul;
    ptr^[1] := NIL;
    RETURN ptr;
  END Arg1;

  PROCEDURE Arg2(a1, a2 : ARRAY OF CHAR) : ArgPtr;
    VAR ptr : ArgPtr; cPtr : CharPtr; ix : CARDINAL;
  BEGIN (* size is 3*ptrs + string-copies *)
    ALLOCATE(ptr,3 * SIZE(CharPtr) + HIGH(a1) + HIGH(a2) + 4);
    cPtr := CAST(CharPtr,ADR(ptr^[3]));
    ptr^[0] := cPtr;
    FOR ix := 0 TO HIGH(a1) DO
      cPtr^ := a1[ix]; cPtr := ADDADR(cPtr,1);
    END;
    cPtr^ := nul; cPtr := ADDADR(cPtr,1);
    ptr^[1] := cPtr;
    FOR ix := 0 TO HIGH(a2) DO
      cPtr^ := a2[ix]; cPtr := ADDADR(cPtr,1);
    END;
    cPtr^ := nul;
    ptr^[2] := NIL;
    RETURN ptr;
  END Arg2;

  PROCEDURE Arg3(a1, a2, a3 : ARRAY OF CHAR) : ArgPtr;
    VAR ptr : ArgPtr; cPtr : CharPtr; ix : CARDINAL;
  BEGIN (* size is 4*ptrs + string-copies *)
    ALLOCATE(ptr,4 * SIZE(CharPtr) + 
               HIGH(a1) + HIGH(a2) + HIGH(a3) + 6);
    cPtr := CAST(CharPtr,ADR(ptr^[4]));
    ptr^[0] := cPtr;
    FOR ix := 0 TO HIGH(a1) DO
      cPtr^ := a1[ix]; cPtr := ADDADR(cPtr,1);
    END;
    cPtr^ := nul; cPtr := ADDADR(cPtr,1);
    ptr^[1] := cPtr;
    FOR ix := 0 TO HIGH(a2) DO
      cPtr^ := a2[ix]; cPtr := ADDADR(cPtr,1);
    END;
    cPtr^ := nul; cPtr := ADDADR(cPtr,1);
    ptr^[2] := cPtr;
    FOR ix := 0 TO HIGH(a3) DO
      cPtr^ := a3[ix]; cPtr := ADDADR(cPtr,1);
    END;
    cPtr^ := nul;
    ptr^[3] := NIL;
    RETURN ptr;
  END Arg3;

  PROCEDURE Arg4(a1, a2, a3, a4 : ARRAY OF CHAR) : ArgPtr;
    VAR ptr : ArgPtr; cPtr : CharPtr; ix : CARDINAL;
  BEGIN (* size is 5*ptrs + string-copies *)
    ALLOCATE(ptr,5 * SIZE(CharPtr) + 
               HIGH(a1) + HIGH(a2) + HIGH(a3) + HIGH(a4) + 8);
    cPtr := CAST(CharPtr,ADR(ptr^[5]));
    ptr^[0] := cPtr;
    FOR ix := 0 TO HIGH(a1) DO
      cPtr^ := a1[ix]; cPtr := ADDADR(cPtr,1);
    END;
    cPtr^ := nul; cPtr := ADDADR(cPtr,1);
    ptr^[1] := cPtr;
    FOR ix := 0 TO HIGH(a2) DO
      cPtr^ := a2[ix]; cPtr := ADDADR(cPtr,1);
    END;
    cPtr^ := nul; cPtr := ADDADR(cPtr,1);
    ptr^[2] := cPtr;
    FOR ix := 0 TO HIGH(a3) DO
      cPtr^ := a3[ix]; cPtr := ADDADR(cPtr,1);
    END;
    cPtr^ := nul; cPtr := ADDADR(cPtr,1);
    ptr^[3] := cPtr;
    FOR ix := 0 TO HIGH(a4) DO
      cPtr^ := a4[ix]; cPtr := ADDADR(cPtr,1);
    END;
    cPtr^ := nul;
    ptr^[4] := NIL;
    RETURN ptr;
  END Arg4;

  PROCEDURE NewArgBlock(VAR b : ArgBlock; cMx : CARDINAL);
  BEGIN
    NEW(b);
    WITH b^ DO
      max := cMx; next := 0;
      ALLOCATE(args, cMx * SIZE(CharPtr));
      ALLOCATE(strs, cMx * SIZE(CharPtr));
      args^[0] := NIL;
    END;
  END NewArgBlock;

  PROCEDURE DisposeArgBlock(VAR b : ArgBlock);
    VAR ix : CARDINAL;
  BEGIN
    WITH b^ DO
      FOR ix := 0 TO next - 1 DO
        DEALLOCATE(strs^[ix], SIZE(CharPtr) + strs^[ix]^.high + 2);
      END;
      DEALLOCATE(args, max * SIZE(CharPtr));
      DEALLOCATE(strs, max * SIZE(CharPtr));
    END;
    DISPOSE(b);
  END DisposeArgBlock;

  PROCEDURE AppendArg(b : ArgBlock;
                      a : ARRAY OF CHAR);
    VAR ix : CARDINAL;
  BEGIN
    WITH b^ DO
      IF next >= max THEN Assert(FALSE) END;
      ALLOCATE(strs^[next], HIGH(a) + SIZE(CARDINAL) + 2);
      WITH strs^[next]^ DO
        high := HIGH(a);
        FOR ix := 0 TO HIGH(a) DO
          chrs[ix] := a[ix];
        END;
        chrs[HIGH(a) + 1] := nul;
        args^[next] := CAST(CharPtr,ADR(chrs));
      END;
      INC(next); args^[next] := NIL;
    END;
  END AppendArg;

  PROCEDURE ArgsOf(b : ArgBlock) : ArgPtr;
  BEGIN
    RETURN b^.args;
  END ArgsOf;

END BuildArgs.
