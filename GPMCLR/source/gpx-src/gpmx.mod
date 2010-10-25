(****************************************************************)
(*                                                              *)
(*                Modula-2 Compiler Source Module               *)
(*                                                              *)
(*                        TEST MODULE                           *)
(*                                                              *)
(*  (c) copyright 1987, 1988 Faculty of Information Technology  *)
(*                                                              *)
(*      original module : kjg May 1988                          *)
(*      modifications   : report usage in verbose mode          *)
(*                                                              *)
(****************************************************************
$Log: gpmd.mod,v $
Revision 1.1  1994/04/07 04:35:47  lederman
Initial revision

****************************************************************)

MODULE GPMx;    (* bare-bones, silent version *)
  IMPORT M2ObjectCode, M2ClrCode, M2ClrTreeToTree, M2TreeToTree;

  FROM ProgArgs        IMPORT UNIXexit;
  FROM M2TabInitialize IMPORT Initialize;
  FROM M2SymParser     IMPORT MakeSymbolFile;
  FROM M2InOut         IMPORT ReportErrors;
  FROM M2Scanner       IMPORT CurrentFlags;
  FROM M2NameHandler   IMPORT Summary;
(*
  FROM M2ObjectCode    IMPORT EmitOutput;
  FROM M2ClrCode       IMPORT EmitOutput;
  FROM M2TreeToTree    IMPORT TransformTree;
  FROM M2ClrTreeToTree IMPORT TransformTree;
 *)
  FROM M2Traversal     IMPORT InitPointers, SemanticCheck;
  FROM M2NodeDefs      IMPORT modState;
  FROM M2MachineConstants IMPORT InitMachineVariables;
  FROM M2Parser        IMPORT
        ParseFileHeader, ParseInputFile;
  FROM M2Alphabets     IMPORT 
        Flags, FlagSet, ModStateFlags, ModStateSet, errors;

  VAR flags : FlagSet;
      objFl : BOOLEAN;

BEGIN
  InitMachineVariables;		(* first initialize config "constants" *)
  Initialize; 			(* then initialize the pervasives etc. *)
  InitPointers;			(* now initialize M2Traversal ptrs     *)
  objFl := FALSE;
  ParseFileHeader;
  ParseInputFile;
  flags := CurrentFlags();
  IF flags * errors = FlagSet{} THEN
    IF defMod IN modState THEN
      MakeSymbolFile;
    ELSE
      SemanticCheck;
      flags := CurrentFlags();
      IF flags * errors = FlagSet{} THEN
        IF emitCil IN modState THEN 
          M2ClrTreeToTree.TransformTree;
        ELSE
          M2TreeToTree.TransformTree;
        END;
        IF objectCode IN modState THEN
          IF emitCil IN modState THEN 
            M2ClrCode.EmitOutput; 
          ELSE 
            M2ObjectCode.EmitOutput; 
          END; 
          objFl := TRUE;
        END;
      END;
    END;
  END;
  flags := CurrentFlags();
  IF  (listings IN flags) OR
      (flags * errors <> FlagSet{}) OR
      (NOT (dangerous IN modState) AND
         (warnings IN flags)) THEN
    ReportErrors();
  END;
  IF superVerbose IN modState THEN Summary() END;
  IF flags * errors <> FlagSet{} THEN UNIXexit(4);  (* Errors              *)
  ELSIF NOT objFl THEN UNIXexit(2);                 (* Finished already    *)
  ELSIF (emitCil IN modState) AND 
        (impMod IN modState) THEN UNIXexit(1);      (* go to ilasm /dll    *)
  ELSE UNIXexit(0);                                 (* go to dgen or ilasm *)
  END;
END GPMx.
