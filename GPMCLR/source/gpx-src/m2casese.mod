(****************************************************************)
(*                                                              *)
(*                Modula-2 Compiler Source Module               *)
(*								*)
(*                Case Statement Selector-list Scan             *)
(*								*)
(*      (c) copyright 1988 Faculty of Information Technology    *)
(*								*)
(*      original module : kjg August 1988                       *)
(*      modifications   : test for max size, density  03-May-89 *)
(*			: case stat in MinAndMax fixed 9-Aug-90 *)
(*			: fix MinAndMax for x-compile  2-Nov-90 *)
(*			: fix calc of size in MinAnd. 29-Jan-91 *)
(*								*)
(****************************************************************
$Log: m2casese.mod,v $
Revision 1.3  1997/01/16 02:32:33  gough
entirely new data structures and algorithms for partitioned tables.

Revision 1.2  1994/08/15 23:56:17  gough
fix up computation of bitmap size for outrageous limits

# Revision 1.1  1994/04/07  04:42:49  lederman
# Initial revision
#
*****************************************************************)

IMPLEMENTATION MODULE M2CaseSelectors;

  IMPORT Ascii, StdError;
  FROM VARSTRS IMPORT APPEND, CUT;
  FROM Storage IMPORT ALLOCATE,DEALLOCATE;

  FROM M2StructureDefs IMPORT
	CaseString, PartString, CRInfo, PrInfo,
        CaseStatDesc, CaseStatRec, (* case statement information *)
        RangeDesc, RangeRec,       (* expression range info.     *)
        CaseDesc, CaseRec;         (* information on single case *)
  FROM M2MachineConstants IMPORT defDensity, optDensity;
  FROM M2Designators IMPORT
        ExprDesc, ExprRec;
  FROM M2SSUtilities IMPORT 
	MinOfOrdType, MaxOfOrdType,
	Compatible, IsSignedType, OrdinalValue;
  FROM M2NodeDefs IMPORT 
	IdDesc, TypeDesc, StrucTree, TyNodeClass, 
	modState, Attribute, AttributeSet, current;
  FROM M2InOut IMPORT Error, Position, lastPos;
  FROM M2Alphabets IMPORT LexAttType, Spellix, ModStateFlags;
  FROM GenSequenceSupport IMPORT
         Sequence, InitCursor, GetNext, Ended, ElemPtr;

(*--------------------------------------------------------------*)
    VAR  densityLimit : INTEGER;
(*--------------------------------------------------------------*)

    VAR sticky : BOOLEAN;

    PROCEDURE RangeTest(selTy : TypeDesc;
			isCrd : BOOLEAN;
			lx,hx : ExprDesc;
		        lv,hv : INTEGER);
    BEGIN
      IF  Compatible(lx^.exprType,selTy) AND
          Compatible(hx^.exprType,selTy) THEN
	IF (lv > hv) AND 		(* probably an error, but ... *)
	  NOT (isCrd AND (lv > 0) AND (hv < 0)) THEN 
          lastPos := hx^.sourceLoc;
          Error(209); sticky := TRUE;
        END;
      ELSE 
        lastPos := lx^.sourceLoc;
        Error(207); sticky := TRUE;
      END; (* if compat ... *)
    END RangeTest;

(*--------------------------------------------------------------*)

    PROCEDURE FindMinAndMax(caseInfo : CaseStatDesc;
                            caseSequ : Sequence);

      VAR caseCurs : ElemPtr;
          casePtr  : CaseDesc;
	  rngeCurs : ElemPtr;
	  rngePtr  : RangeDesc;
	  string   : CaseString;
	  partStr  : PartString;
	  isCard   : BOOLEAN;
	  srcLoc   : Position;
	  selType  : TypeDesc;

	  loRng    : INTEGER;
	  hiRng    : INTEGER;

      PROCEDURE QuickSort(str : CaseString; l,r : INTEGER);
	VAR i,j : INTEGER;
	    key : INTEGER;
	    tmp : CRInfo;
      BEGIN
	i := l; j := r;
	key := str[(l+r) DIV 2].min;
	REPEAT
	  WHILE str[i].min < key DO INC(i) END;
	  WHILE str[j].min > key DO DEC(j) END;
	  IF i <= j THEN
	    tmp := str[i]; str[i] := str[j]; str[j] := tmp; INC(i); DEC(j);
	  END;
	UNTIL i > j;
	IF l < j THEN QuickSort(str,l,j) END;
	IF i < r THEN QuickSort(str,i,r) END;
      END QuickSort;

      PROCEDURE Compress(str : CaseString; lo,hi : INTEGER);
        VAR ri, wi : INTEGER;	(* read index, write index *)
	    mn, mx : INTEGER;   (* min and max of current  *)
	    casPtr : CaseDesc;  (* the current case record *)
      BEGIN
	wi := -1;
	mn := str[0].min;
	mx := str[0].max;
	casPtr := str[0].cas;
	FOR ri := 1 TO HIGH(str) DO
	  IF (str[ri].min = mx + 1) AND 
	     (str[ri].cas = casPtr) THEN (* update current range *)
	    mx := str[ri].max;
	  ELSIF str[ri].min > mx THEN    
	   (*
	    *  Write out the current range, clipped
	    *  to the selector expression type-range.
	    *)
	    IF mn < lo THEN mn := lo END;
	    IF hi < mx THEN mx := hi END;
	    IF mn <= mx THEN
	      INC(wi);
	      str[wi].min := mn;
	      str[wi].max := mx;
	      str[wi].cas := casPtr;
	    END;
	    mn := str[ri].min;
	    mx := str[ri].max;
	    casPtr := str[ri].cas;
	  ELSE (* duplicated value *)
            lastPos := str[ri].pos; 
	    Error(267); sticky := TRUE; RETURN;
	  END;
	END;
       (*
	*  Write out the final range, clipped
	*  to the selector expression type-range.
	*)
	IF mn < lo THEN mn := lo END;
	IF hi < mx THEN mx := hi END;
	IF mn <= mx THEN
	  INC(wi);
	  str[wi].min := mn;
	  str[wi].max := mx;
	  str[wi].cas := casPtr;
	END;
	CUT(str,wi);
        IF superVerbose IN modState THEN DiagString(str) END;
      END Compress;

      PROCEDURE Partition(str : CaseString; prt : PartString);

	PROCEDURE TryMerger(prt : PartString; lim : REAL);
	  VAR hip : INTEGER;
	      tot : CARDINAL;
	BEGIN
	  hip := HIGH(prt);
	  tot := prt[hip].num + prt[hip-1].num;
   (* $T- *)
	  IF FLOAT(tot) / FLOAT(prt[hip].max - prt[hip-1].min + 1) > lim THEN
	    prt[hip-1].num := tot;
	    prt[hip-1].max := prt[hip].max;
	    prt[hip-1].xIx := prt[hip].xIx;
	    CUT(prt,hip-1);
	    IF hip > 1 THEN TryMerger(prt,lim) END;    
	  END;
   (* $T= *)
	END TryMerger;

	VAR i     : INTEGER;
	    pMin  : INTEGER;
	    pMax  : INTEGER;
	    totE  : CARDINAL;
	    limit : REAL;

      BEGIN
	IF HIGH(str) < 3 THEN 
	  limit := 0.0;
        ELSE 
	  limit := FLOAT(densityLimit) / 16.0;
	END;

	IF HIGH(str) >= 0 THEN
   (* $T- *
	  *  By construction, (max - min) >= 0, but might exceed maxint.
	  *  Thus performing the arithmetic modulo-2^32 is ok.
	  *)
	  pMin := str[0].min;
	  pMax := str[0].max;
	  totE := pMax - pMin + 1;
	  APPEND(prt,PrInfo{totE,pMin,pMax,0,0});
	  FOR i := 1 TO HIGH(str) DO
	    pMin := str[i].min;
	    pMax := str[i].max;
	    totE := pMax - pMin + 1;
	    APPEND(prt,PrInfo{totE,pMin,pMax,i,i});
	    TryMerger(prt,limit);
	  END;
   (* $T= *)
	END;
        IF superVerbose IN modState THEN DiagPartition(str,prt) END;
      END Partition;

PROCEDURE StdErrorWriteInt(i : INTEGER);
BEGIN
 (* $T- *)
 (* $R- *)
  IF i < 0 THEN StdError.Write("-"); i := -i END;
  StdError.WriteCard(i,0);
 (* $R= *)
 (* $T= *)
END StdErrorWriteInt;

PROCEDURE DiagPartition(str : CaseString; prt : PartString);
  VAR ri : INTEGER;
      si : INTEGER;
BEGIN
StdError.WriteString("======================");
StdError.WriteLn;
FOR ri := 0 TO HIGH(prt) DO
  StdError.WriteString("partition");
  FOR si := prt[ri].nIx TO prt[ri].xIx DO
    StdError.Write(" ");
    StdErrorWriteInt(str[si].min);
    IF str[si].max <> str[si].min THEN
      StdError.WriteString(" .. ");
      StdErrorWriteInt(str[si].max);
    END;
    StdError.Write(",");
  END;
  StdError.WriteLn;
END;
END DiagPartition;

PROCEDURE DiagString(str : CaseString);
  VAR si : INTEGER;
BEGIN
StdError.WriteString("=====string======");  StdError.WriteLn;
FOR si := 0 TO HIGH(str) DO
  StdErrorWriteInt(str[si].min);
  IF str[si].max <> str[si].min THEN
    StdError.WriteString(" .. ");
    StdErrorWriteInt(str[si].max);
  END;
  StdError.Write(",");
  IF si MOD 16 = 15 THEN StdError.WriteLn ELSE StdError.Write(" ") END;
END;
StdError.WriteLn;
END DiagString;

    BEGIN (* FindMinAndMax *)
     (*
      *  Expressions have already been traversed, and folded.
      *)
      sticky := FALSE;
      IF optimize IN current^.body^.callAttrib THEN 
	densityLimit := optDensity;
      ELSE 
	densityLimit := defDensity;
      END;

      isCard  := NOT IsSignedType(caseInfo^.switch^.exprType);
      selType := caseInfo^.switch^.exprType;
      InitCursor(caseSequ,caseCurs);
      WHILE NOT Ended(caseCurs) DO
	GetNext(caseCurs,casePtr);
	InitCursor(casePtr^.selRnges,rngeCurs);
	WHILE NOT Ended(rngeCurs) DO
	  GetNext(rngeCurs,rngePtr);
	  (* $R- *)
	  loRng := OrdinalValue(selType,rngePtr^.lower^.conValue);
	  hiRng := OrdinalValue(selType,rngePtr^.upper^.conValue);
	  RangeTest(selType,isCard,rngePtr^.lower,rngePtr^.upper,loRng,hiRng);
	  (* $R= *)
	  srcLoc := rngePtr^.upper^.sourceLoc;
	  IF loRng > hiRng THEN (* split the wrapped range *)
	    APPEND(caseInfo^.caseStr,
			CRInfo{MIN(INTEGER),hiRng,srcLoc,casePtr});
	    hiRng := MAX(INTEGER);
	  END;
	  APPEND(caseInfo^.caseStr,
			CRInfo{loRng,hiRng,srcLoc,casePtr});
	END;
      END;
      IF NOT sticky THEN 
     (*
      * IF superVerbose IN modState THEN DiagString(caseInfo^.caseStr) END;
      *)
        QuickSort(caseInfo^.caseStr,0,HIGH(caseInfo^.caseStr));
       (* handle that pesky cardinal possibility *)
       (* $R- *)
        loRng := MinOfOrdType(selType);
        hiRng := MaxOfOrdType(selType);
       (* $R= *)
        IF hiRng < loRng THEN loRng := MIN(INTEGER); hiRng := MAX(INTEGER) END;
       (* now compress the table *)
        Compress(caseInfo^.caseStr,loRng,hiRng);
        IF NOT sticky THEN 
          Partition(caseInfo^.caseStr,caseInfo^.partStr);
        END;
      END;
    END FindMinAndMax;

END M2CaseSelectors.
