(****************************************************************)
(*                                                              *)
(*         Gardens Point Modula-2 Library Definition            *)
(*                                                              *)
(*                                                              *)
(*     (c) Copyright 1996 Faculty of Information Technology     *)
(*              Queensland University of Technology             *)
(*                                                              *)
(*     Permission is granted to use, copy and change this       *)
(*     program as long as the copyright message is left intact  *)
(*     M2 version KJG November 2003                             *)
(*                                                              *)
(****************************************************************)

IMPLEMENTATION MODULE AsciiTime;

   (* ========================================================= *)
   (*  This module converts Time in the structure specified in  *)
   (*  the MODULE SysClock into a printable ascii string.       *)
   (*  There is also a procedure for converting time in the     *)
   (*  "seconds since 1970 " cardinal form, into a DateTime     *)
   (*  structure.                                               *)
   (*                                                           *)
   (*  Note : This module is useful in conjunction with the     *)
   (*  the procedures for obtaining the time that are present   *)
   (*  in the UxFiles, and ProgArgs MODULES.                    *) 
   (*                                                           *)
   (* ========================================================= *)

  FROM SysClock IMPORT DateTime, DateTimeFromUnixTime;

  PROCEDURE StructTimeToAscii(VAR str : ARRAY OF CHAR; time : DateTime);
  (*
   * Places ascii representation of 'time' in 'str'. If there is
   * not enough room in 'str' then the representation is truncated
   * as required by the string's length. If there is adequate length
   * then the string is terminated with a null character.
   *)
    VAR buff : ARRAY [0 .. 24] OF CHAR;
        indx : CARDINAL;

    PROCEDURE Insert(VAR buff : ARRAY OF CHAR; 
                         valu : CARDINAL;
                         rIdx : INTEGER);
    BEGIN
      WHILE valu > 0 DO
        buff[rIdx] := CHR(valu MOD 10 + ORD('0'));
        valu := valu DIV 10;
        DEC(rIdx);
      END;
    END Insert;

  BEGIN
    (* ===== 0123456789012345678901234 *)
    buff := "0000:00:00::00:00:00 UTC";
    (* ===== 0123456789012345678901234 *)
    Insert(buff, time.year,    3);
    Insert(buff, time.month,   6);
    Insert(buff, time.day,     9);
    Insert(buff, time.hour,   13);
    Insert(buff, time.minute, 16);
    Insert(buff, time.second, 19);
    FOR indx := 0 TO 24 DO
      IF indx <= HIGH(str) THEN str[indx] := buff[indx];
      ELSE RETURN; (* =============== FORCED EXIT OF LOOP ================== *)
      END;
    END;
  END StructTimeToAscii;


  PROCEDURE TimeToStructTime(time : CARDINAL; VAR structTime : DateTime);
  (* Converts time cardinals into the structured form. *)
  BEGIN
    DateTimeFromUnixTime(time, structTime);
  END TimeToStructTime;

END AsciiTime. 
