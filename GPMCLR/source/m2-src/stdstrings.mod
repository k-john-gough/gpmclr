
(* ========================================================= *)
(* Preliminary library module for Gardens Point Modula       *)
(* ========================================================= *)

IMPLEMENTATION MODULE StdStrings; (* kjg june 1989 *)

(* $I- *) (* $R- *) (* $F+ *)

(* this implementation conforms to the May 89 ISO draft *)

  IMPORT Ascii;
  FROM SYSTEM IMPORT INCADR, DECADR, DIFADR, ADR, CAST;

(*
   exported types are ---

   TYPE String1 = ARRAY [0 .. 0] OF CHAR;

   CONST StringCapacity = 256;

   TYPE String  = ARRAY [0 .. StringCapacity - 1] OF CHAR;

   TYPE CompareResult : (less, equal, greater);
*)

TYPE CharPtr = POINTER TO CHAR;

PROCEDURE Length (str : ARRAY OF CHAR) : CARDINAL;
  VAR ix : CARDINAL;
BEGIN
  ix := 0;
  WHILE (ix <= HIGH(str)) AND
        (str[ix] <> Ascii.nul) DO INC(ix) END;
  (* post : ix is length of string *)
  RETURN ix;
END Length;

PROCEDURE CanAssignAll 
              ( sourceLength : CARDINAL;
             VAR destination : ARRAY OF CHAR) : BOOLEAN;
BEGIN
  RETURN HIGH(destination) > sourceLength;
END CanAssignAll;

PROCEDURE Assign    ( source : ARRAY OF CHAR;
             VAR destination : ARRAY OF CHAR);
  VAR ix, smaller : CARDINAL; ch : CHAR;
BEGIN
  IF HIGH(source) < HIGH(destination) THEN
    smaller := HIGH(source);
  ELSE smaller := HIGH(destination);
  END;
  FOR ix := 0 TO smaller DO
    ch := source[ix];
    destination[ix] := ch;
    IF ch = Ascii.nul THEN RETURN END;
  END;
  IF smaller < HIGH(destination) THEN
    destination[smaller + 1] := Ascii.nul;
  END;
END Assign;


PROCEDURE CanExtractAll( len : CARDINAL;
	                 sIx : CARDINAL;
		         num : CARDINAL;
		     VAR dst : ARRAY OF CHAR) : BOOLEAN;
BEGIN
  RETURN  (sIx + num <= len) AND (HIGH(dst) + 1 >= num);
END CanExtractAll;

PROCEDURE Extract   ( source : ARRAY OF CHAR;
	                 sIx : CARDINAL;
		         num : CARDINAL;
		     VAR dst : ARRAY OF CHAR);
  VAR ch : CHAR; dIx, lim : CARDINAL;
BEGIN
  dIx := 0;
  IF num > 0 THEN (* else special case *)
    DEC(num);
    IF num > HIGH(dst) THEN num := HIGH(dst) END;
    lim := 0;
    WHILE (lim <= HIGH(source)) AND
          (source[lim] <> Ascii.nul) DO INC(lim) END;
    (* post : lim is length of string *)
    IF sIx + num >= lim THEN DEC(lim);
    ELSE lim := sIx + num;
    END;
    (* post : lim is last index to copy *)
    WHILE sIx <= lim DO
      dst[dIx] := source[sIx]; INC(sIx); INC(dIx);
    END;
  END;
  IF dIx <= HIGH(dst) THEN dst[dIx] := Ascii.nul END;
END Extract;

PROCEDURE CanDeleteAll ( len : CARDINAL;
			 sIx : CARDINAL;
			 num : CARDINAL) : BOOLEAN;
BEGIN
  RETURN (sIx < len) AND (sIx + num <= len);
END CanDeleteAll;

PROCEDURE Delete (VAR string : ARRAY OF CHAR;
			 sIx : CARDINAL;
			 num : CARDINAL);
  VAR lim, mIx : CARDINAL;
BEGIN
  lim := 0;
  WHILE (lim <= HIGH(string)) AND
        (string[lim] <> Ascii.nul) DO INC(lim) END;
  (* post : lim is length of string *)
  IF sIx < lim THEN (* else do nothing *)
    IF sIx + num <= lim THEN (* else sIx is unchanged *)
      mIx := sIx + num;
      WHILE mIx < lim DO
        string[sIx] := string[mIx]; INC(sIx); INC(mIx);
      END;
    END;
    IF sIx <= HIGH(string) THEN string[sIx] := Ascii.nul END;
  END;
END Delete;

PROCEDURE CanInsertAll (sLen : CARDINAL;
			 sIx : CARDINAL;
		     VAR dst : ARRAY OF CHAR) : BOOLEAN;
  VAR dLen : CARDINAL;
BEGIN
  dLen := 0;
  WHILE (dLen <= HIGH(dst)) AND
        (dst[dLen] <> Ascii.nul) DO INC(dLen) END;
  (* post : dLen is length of string *)
  RETURN (sIx < dLen) AND (dLen + sLen <= HIGH(dst) + 1);
END CanInsertAll;

PROCEDURE Insert    ( source : ARRAY OF CHAR;
			 sIx : CARDINAL;
		     VAR dst : ARRAY OF CHAR);
  VAR dLen, sLen, rIx : CARDINAL; 
      copyDst : BOOLEAN;
      ix : CARDINAL;
BEGIN
  (* skip trivial case *)
  IF sIx >= HIGH(dst) THEN RETURN END;
  (* first find sLen *)
  sLen := 0;
  WHILE (sLen <= HIGH(source)) AND
        (source[sLen] <> Ascii.nul) DO INC(sLen) END;
  (* skip trivial case *)
  IF sLen = 0 THEN RETURN END;
  (* now check that dLen >= sIx *)
  dLen := 0;
  WHILE (dLen <= HIGH(dst)) AND (dst[dLen] <> Ascii.nul) DO 
    INC(dLen);
  END;
  IF dLen < sIx THEN RETURN END;
  (* now copy excess characters up *)
  rIx := dLen + sLen;
  IF rIx > HIGH(dst) THEN
    rIx := HIGH(dst); 
    IF rIx >= sLen THEN copyDst := TRUE;
    ELSE
      copyDst := FALSE;
      dLen := rIx - sLen;
    END;
  ELSE 
    dst[rIx] := Ascii.nul; 
    DEC(rIx); DEC(dLen);
    copyDst := TRUE;
  END;
  IF copyDst THEN
    FOR ix := dLen TO sIx BY -1 DO
      dst[rIx] := dst[ix]; DEC(rIx);
    END;
  END;
  (* now copy in source string *)
  DEC(sLen); (* assert : was not zero previously *)
  IF sLen + sIx > HIGH(dst) THEN sLen := HIGH(dst) - sIx END;
  FOR dLen := 0 TO sLen DO
    dst[sIx] := source[dLen]; INC(sIx);
  END;
END Insert;

PROCEDURE CanReplaceAll( len : CARDINAL;
			 sIx : CARDINAL;
		     VAR dst : ARRAY OF CHAR) : BOOLEAN;
  VAR dLen : CARDINAL;
BEGIN
  dLen := 0;
  WHILE (dLen <= HIGH(dst)) AND
        (dst[dLen] <> Ascii.nul) DO INC(dLen) END;
  (* post : dLen is length of string *)
  RETURN len + sIx <= dLen;
END CanReplaceAll;

PROCEDURE Replace   ( source : ARRAY OF CHAR;
			 sIx : CARDINAL;
		     VAR dst : ARRAY OF CHAR);
  VAR dLen, ix : CARDINAL;
BEGIN
  dLen := 0;
  IF sIx > HIGH(dst) THEN RETURN END;
  WHILE (dLen < sIx) AND
        (dst[dLen] <> Ascii.nul) DO INC(dLen) END;
  IF dLen <> sIx THEN RETURN END;
  ix := 0;
  WHILE (ix <= HIGH(source)) AND 
	(sIx <= HIGH(dst)) AND 
	(source[ix] <> Ascii.nul) AND
	(dst[ix] <> Ascii.nul) DO
    dst[sIx] := source[ix]; INC(ix); INC(sIx);
  END;
END Replace;

PROCEDURE CanAppendAll(len : CARDINAL;
                   VAR dst : ARRAY OF CHAR) : BOOLEAN;
  VAR ix : CARDINAL;
BEGIN
  ix := 0;
  WHILE (ix <= HIGH(dst)) AND
        (dst[ix] <> Ascii.nul) DO INC(ix) END;
  (* post : ix is length of string *)
  (* assert : HIGH(dst) + 1 >= ix *)
  RETURN HIGH(dst) + 1 >= ix + len;
END CanAppendAll;

PROCEDURE Append(src : ARRAY OF CHAR;
             VAR dst : ARRAY OF CHAR);
  VAR sIx, dIx, smaller : CARDINAL; ch : CHAR;
BEGIN
  sIx := 0; dIx := 0;
  WHILE (dIx <= HIGH(dst)) AND
        (dst[dIx] <> Ascii.nul) DO INC(dIx) END;
  (* post : dIx is length of dst string *)

  IF HIGH(dst) > HIGH(src) + dIx THEN
    smaller := HIGH(src) + dIx;
  ELSE smaller := HIGH(dst);
  END;
  WHILE dIx <= smaller DO
    ch := src[sIx];
    dst[dIx] := ch;
    IF ch = Ascii.nul THEN RETURN END;
    INC(sIx); INC(dIx);
  END;
  IF dIx <= HIGH(dst) THEN
    dst[dIx] := Ascii.nul;
  END;
END Append;

PROCEDURE Capitalize(VAR str : ARRAY OF CHAR);
  VAR ix : CARDINAL;
BEGIN
  ix := 0;
  WHILE (ix <= HIGH(str)) AND (str[ix] <> Ascii.nul) DO
    str[ix] := CAP(str[ix]);
    INC(ix);
  END;
END Capitalize;

(*
 *   There are two different versions of Compare here.
 *   They use different algorithms which have been
 *   tuned for statistically good behaviour. The first
 *   one is usually faster, but neither is as good
 *   as the C strcmp, due to the need to check HIGH.
 *   It is possible to do things much simpler, and 
 *   pay a 30% penalty ...
 *
 *   These routines must be compiled with (* $F+ *)
 *   in order to optimize the value params with gpm. On
 *   other M2 compilers the performance will suffer due
 *   to the value array copying. In such cases it is
 *   best to substitute the implementation string compare.
 *)

PROCEDURE Compare      (str1 : ARRAY OF CHAR;
			str2 : ARRAY OF CHAR) : CompareResult;
  VAR s1, s2 : CHAR; ix, lim : CARDINAL;
BEGIN
  IF str1[0] <> str2[0] THEN 
    IF str1[0] < str2[0] THEN RETURN less;
    ELSE RETURN greater;
    END;
  ELSIF str1[0] = Ascii.nul THEN RETURN equal;
  ELSE
    IF HIGH(str1) <= HIGH(str2) THEN lim := HIGH(str1);
    ELSE lim := HIGH(str2);
    END;
    s1 := str1[1]; s2 := str2[1]; ix := 1;
    IF (str1[lim] <> str2[lim]) OR (str2[lim] = Ascii.nul) THEN
      LOOP
        IF s1 = s2 THEN
	  IF s2 = Ascii.nul THEN RETURN equal END;
	  INC(ix); s1:= str1[ix]; s2 := str2[ix];
        ELSIF s1 < s2 THEN RETURN less;
        ELSE RETURN greater;
        END;
      END;
    ELSE
      WHILE ix <= lim DO
        IF s1 = s2 THEN
	  IF s2 = Ascii.nul THEN RETURN equal END;
	  INC(ix); s1:= str1[ix]; s2 := str2[ix];
        ELSIF s1 < s2 THEN RETURN less;
        ELSE RETURN greater;
        END;
      END;
    END;
    (* assert: ix = lim + 1 *)
    IF (HIGH(str2) > lim) THEN
      IF s2 <> Ascii.nul THEN RETURN less;
      ELSE RETURN equal;
      END;
    ELSIF HIGH(str1) > lim THEN
      IF s1 <> Ascii.nul THEN RETURN greater;
      ELSE RETURN equal;
      END;
    ELSE RETURN equal;
    END;
  END;
END Compare;

(*
PROCEDURE Compare      (str1 : ARRAY OF CHAR;
			str2 : ARRAY OF CHAR) : CompareResult;
  VAR s1, s2 : CHAR; ix, lim, lim1, lim2 : CARDINAL;
BEGIN
  IF str1[0] <> str2[0] THEN 
    IF str1[0] > str2[0] THEN RETURN less;
    ELSE RETURN greater;
    END;
  ELSE 
    IF str1[0] = Ascii.nul THEN RETURN equal END;
    lim1 := HIGH(str1) + 1;
    lim2 := HIGH(str2) + 1;
    s1 := str1[1]; s2 := str2[1]; ix := 1;
    IF str2[lim2] = Ascii.nul THEN (* simple is safe *)
      WHILE s1 = s2 DO
	IF s1 = Ascii.nul THEN RETURN equal END;
	INC(ix); s1 := str1[ix]; s2 := str2[ix];
      END;
      (* chars are different *)
      IF ix >= lim1 THEN
	IF s2 = Ascii.nul THEN RETURN equal;
        ELSE RETURN less;
	END;
      ELSIF s1 < s2 THEN RETURN less;
      ELSE RETURN greater;
      END;
    ELSIF str1[lim1] = Ascii.nul THEN (* simple is safe *)
      WHILE s1 = s2 DO
	IF s1 = Ascii.nul THEN RETURN equal END;
	INC(ix); s1 := str1[ix]; s2 := str2[ix];
      END;
      (* chars are different *)
      IF ix >= lim2 THEN
	IF s1 = Ascii.nul THEN RETURN equal;
        ELSE RETURN greater;
	END;
      ELSIF s1 < s2 THEN RETURN less;
      ELSE RETURN greater;
      END;
    ELSE (* must do full test *)
      IF lim1 <= lim2 THEN lim := lim1 ELSE lim := lim2 END;
      WHILE ix < lim DO
	IF s1 = s2 THEN
	  IF s2 = Ascii.nul THEN RETURN equal;
	  ELSE INC(ix); s1 := str1[ix]; s2 := str2[ix];
	  END;
        ELSIF s1 < s2 THEN RETURN less;
        ELSE RETURN greater;
        END;
      END;
      IF lim2 > lim THEN (* only lim1 is known to be ended *)
        IF s2 <> Ascii.nul THEN RETURN less;
        ELSE RETURN equal;
        END;
      ELSIF lim1 > lim THEN
        IF s1 <> Ascii.nul THEN RETURN greater;
        ELSE RETURN equal;
        END;
      ELSE RETURN equal;
      END;
    END;
  END;
END Compare;
*)

PROCEDURE FindNext     ( pat : ARRAY OF CHAR;
			 str : ARRAY OF CHAR;
			 sIx : CARDINAL;
		     VAR fnd : BOOLEAN;
		     VAR pos : CARDINAL);
  VAR px, sx : CARDINAL;
BEGIN
  (* first check that string extends to sIx *)
  IF sIx > HIGH(str) THEN fnd := FALSE; RETURN END;
  px := 0;
  WHILE (px < sIx) AND (str[px] <> Ascii.nul) DO INC(px) END;
  IF px < sIx THEN fnd := FALSE; RETURN END;
  (* now find potential starting points *)
  WHILE (sIx <= HIGH(str)) AND (str[sIx] <> Ascii.nul) DO
    IF str[sIx] = pat[0] THEN
      (* now compare strings *)
      px := 0; sx := sIx;
      LOOP
	INC(px); INC(sx);
	IF (px > HIGH(pat)) OR (pat[px] = Ascii.nul) THEN
	  fnd := TRUE; pos := sIx; RETURN;
	ELSIF (sx > HIGH(str)) OR (str[sx] = Ascii.nul) THEN
	  fnd := FALSE; RETURN;
	ELSIF pat[px] <> str[sx] THEN EXIT;
	END;
      END;
    END;
    INC(sIx);
  END; (* outer while *)
  fnd := FALSE;
END FindNext;

PROCEDURE FindPrev     ( pat : ARRAY OF CHAR;
			 str : ARRAY OF CHAR;
			 sIx : CARDINAL;
		     VAR fnd : BOOLEAN;
		     VAR pos : CARDINAL);
  VAR ix, sx, px : CARDINAL;
BEGIN
(* 
   what is the required semantics here?
   do you start searching from sIx, or from sIx - 1 ?
*)
  ix := 0;
  (* first check that string extends to sIx *)
  IF sIx > HIGH(str) THEN sIx := HIGH(str) END;
  WHILE (ix <= sIx) AND (str[ix] <> Ascii.nul) DO INC(ix) END;
  (* assert: ix is one past end, or one past sIx *)
  (* now find potential starting points *)
  WHILE ix > 0 DO
    DEC(ix); (* looks for pattern starting at or before sIx *)
    IF str[sIx] = pat[0] THEN
      (* now compare strings *)
      px := 0; sx := sIx;
      LOOP
	INC(px); INC(sx);
	IF (px > HIGH(pat)) OR (pat[px] = Ascii.nul) THEN
	  fnd := TRUE; pos := ix; RETURN;
	ELSIF (sx > HIGH(str)) OR 
	      (str[sx] = Ascii.nul) OR
	      (pat[px] <> str[sx]) THEN EXIT;
	END;
      END;
    END;
  END; (* outer while *)
  fnd := FALSE;
END FindPrev;

PROCEDURE FindDiff    ( str1 : ARRAY OF CHAR;
			str2 : ARRAY OF CHAR;
		    VAR diff : BOOLEAN;
		    VAR dPos : CARDINAL);
  VAR ix : CARDINAL;
BEGIN
  ix := 0;
  IF (str1[ix] = str2[ix]) THEN 
    IF str1[ix] = Ascii.nul THEN (* both strings empty *)
      diff := FALSE; RETURN;
    END;
    LOOP
      INC(ix);
      IF (ix > HIGH(str1)) OR (str1[ix] = Ascii.nul) THEN (* 1 ended *)
        IF (ix > HIGH(str2)) OR (str2[ix] = Ascii.nul) THEN (* 2 also *)
	  diff := FALSE; RETURN; (* both ended, and equal *)
	ELSE EXIT; (* only 1 ended *)
	END;
      ELSIF (ix > HIGH(str2)) OR (str2[ix] = Ascii.nul) THEN 
	EXIT; (* only 2 ended *)
      ELSIF str1[ix] <> str2[ix] THEN
	EXIT; (* strings differ *)
      (* else go around the loop once more *)
      END;
    END;
  END;
  diff := TRUE; dPos := ix;
END FindDiff;

END StdStrings.
