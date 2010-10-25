(****************************************************************)
(*                                                              *)
(*              Modula-2 Compiler Source Module                 *)
(*                                                              *)
(*                 Runtime System Interface			*)
(*                                                              *)
(*     (c) copyright 1990 Faculty of Information Technology     *)
(*                                                              *)
(*      original module : kjg January 1990                      *)
(*      modifications   : dwc 1/91 m2_time changed to UNIXtime  *)
(****************************************************************
$Log: m2rtsint.mod,v $
Revision 1.4  1997/01/20 01:39:15  behrooz
getting the last one right after all

Revision 1.3  1997/01/20 01:11:25  behrooz
insert string name for m2_preTrp = "_gp_preTrp"

Revision 1.2  1996/11/27 02:47:35  lederman
change "exit" to "ProgArgs_UNIXexit";  remove rts array

Revision 1.1  1994/04/07 05:15:12  lederman
Initial revision

*****************************************************************)

IMPLEMENTATION MODULE M2RTSInterface;
  FROM M2NameHandler IMPORT EnterString;

  PROCEDURE InitTable;
  BEGIN
    EnterString("_gp_rTrpLI",m2_rTrpLI);
    EnterString("_gp_rTrpHU",m2_rTrpHU);
    EnterString("_gp_modTrp",m2_modTrp);
    EnterString("_gp_casTrp",m2_casTrp);
    EnterString("_gp_funTrp",m2_funTrp);
    EnterString("_gp_preTrp",m2_preTrp);
    EnterString("_gp_assTrp",m2_assTrp);
    EnterString("_gp_iTrpLHI",m2_iTrpLHI);
    EnterString("_gp_iTrpLHU",m2_iTrpLHU);
    EnterString("_gp_rTrpLHI",m2_rTrpLHI);
    EnterString("_gp_rTrpLHU",m2_rTrpLHU);
    EnterString("_eVec",eVec);
    EnterString("_fVec",fVec);
    EnterString("_geq",geq);
    EnterString("_leq",leq);
    EnterString("_equ",equ);
    EnterString("_neq",neq);

    EnterString("_clr",clr);
    EnterString("_cap2",cap2);
    EnterString("_cap3",cap3);
    EnterString("_cup2",cup2);
    EnterString("_cup3",cup3);
    EnterString("_xor2",xor2);
    EnterString("_xor3",xor3);
    EnterString("_dif2",dif2);
    EnterString("_dif3",dif3);
    EnterString("_setRngIncl",setRngIncl);
    EnterString("_strLen",strLen);

    EnterString("ProgArgs_UNIXexit",exitTrp);
    EnterString("abort",abortTrp);
    EnterString("_gp_timTrp",timeTrp);

  END InitTable;

END M2RTSInterface.
