(****************************************************************)
(*                                                              *)
(*              Modula-2 Compiler Source Module                 *)
(*                                                              *)
(*         Code Generation and CIL Assembly Code Output         *)
(*                                                              *)
(*     (c) copyright 2003 Faculty of Information Technology     *)
(*                                                              *)
(*      original module : kjg January 1990                      *)
(*      modifications   : CIL version kjg June 2003             *)
(*								*)
(****************************************************************)

IMPLEMENTATION MODULE M2CILwriter;

  IMPORT M2IL, Ascii, HugeInts, StdError, SYSTEM, Storage, Types;

  FROM ProgArgs IMPORT Assert, FP_Overflow;

  FROM Types IMPORT Card8, Card16, Card32;

  FROM M2IL  IMPORT 
        ModeEnum, Relops, LabelType, Object, Instruction, InstructionTable;

  FROM VARSTRS IMPORT APPEND, CUT;
  FROM Storage IMPORT ALLOCATE, DEALLOCATE;

  FROM GenSequenceSupport IMPORT 
        ElemPtr, InitCursor, GetNext, Sequence, InitSequence, 
        LinkRight, LengthOf, Ended;

  FROM M2NodeDefs IMPORT
        CreateIdDesc, CreateTypeDesc,
        UsesSet, VarUses, TyString, IdString, PubEnum, 
        modState, FormalType, FormalClass, IdDesc, StrucTree,
        Attribute, AttributeSet, TypeDesc, FormalType, IdDesc,
        IdTree, TyNodeClass, TyClassSet, IdNodeClass, IdClassSet,
        thisCompileUnit, pervasiveUnit, globalModList;

  FROM M2LitChain IMPORT
        chainHead, chainTail, ConstDataSize;

  FROM M2Designators IMPORT 
        AccessMode, ExprDesc, ExprRec, ExprNodeClass, ExpandInfo;

  FROM M2Alphabets IMPORT 
        Spellix, LexAttType, HashBucketType, ModStateFlags, 
        ModStateSet, ConBlock;

  FROM M2InOut IMPORT 
        DiagName, WriteObjByte, inpName,
        EmitFileName, lastPos, ErrIdent, debugOn;

  FROM M2NameHandler IMPORT 
        anonBkt, EnterString, StringTable, GetSourceRep, GetString;

  FROM M2MachineConstants IMPORT 
        stackMarkSize, bytesInWord, adrSize, extRecRetPtr, 
        extArrRetPtr, parsFixed, bytesInReal, bigEndian, 
        crossEndian, destOffset, gdbSupport, exceptOK, INFINITY;

  FROM M2SSUtilities IMPORT LookupInThisScope, IsSignedType, IsStringType, Align;
  FROM M2RTSInterface IMPORT equ, neq, geq, leq;
  FROM M2TabInitialize IMPORT PointerTo;

(*====================================================*)

  CONST ilManaged  = " cil managed";
        RTSname    = "M2ClrRts";

  TYPE  StringType = ARRAY [0 .. 127] OF CHAR;

  TYPE  FormSet    = SET OF FormalClass;

  VAR   thisName : StringType;
        jumpSeq  : Sequence;

        conDatB  : HashBucketType;
        modNamB  : HashBucketType;
        rtsBkt   : HashBucketType;
        sPtrBkt  : HashBucketType;
        cctorBkt : HashBucketType;
        catchBkt : HashBucketType;

        hiType   : TypeDesc;
        aliasInf : BOOLEAN;

(*====================================================*)

(*====================================================*)

    TYPE   ExprNodeMap = ARRAY [0 .. 6] OF Relops;

    CONST  eqOrd = ORD(equalsNode);
           exprNodeToRelop = ExprNodeMap{eqR, neR, gtR, geR, lsR, leR, inR};

    TYPE   RelopTable = ARRAY [0..5] OF Instruction;

(*====================================================*)

    CONST allProcs     = IdClassSet{procNode,procHeader,externProc,cilWrapper};

(*====================================================*)
  MODULE WriteDASM;

    IMPORT 
        M2IL, SYSTEM, HugeInts, Ascii, 
        GetSourceRep, modState, ModStateFlags,
        Instruction, WriteObjByte, Card8, 
        thisName, EmitFileName, 
        StringType, IdDesc, HashBucketType;

    EXPORT 
        BuffS, BuffN, QuStr, BuffH, BuffI, BuffIx, BuffHuge,
        WriteComment, CommentBegin, CommentStart, CommentEnd,
        BuffInt, BuffCrd, BuffEol, Ampersand,
        Space, Dot, Comma, HTab, DColon, Star, getModule,
        LBrace, RBrace, LBrace2, RBrace2, WriteByte, 
        NamespaceBegin, NamespaceEnd, 
        ZeroStack, MaxStack, SetRetAdjust, Return,
        WriteGreeting, WriteHeaderRecord;

(* ==================================================== *)
(*  The following fields are global variables of the    *)
(*  current method emission.  For re-entrance they      *)
(*  should be instance data.  But GPM is not threaded.  *)
(* ==================================================== *)

  VAR thisModule : IdDesc;
      thisHeight : INTEGER;
      maxHeight  : INTEGER;
      retAdjust  : INTEGER;

(* ==================================================== *)

  PROCEDURE SetModule(m : IdDesc);
  BEGIN thisModule := m END SetModule;

  PROCEDURE getModule() : IdDesc;
  BEGIN RETURN thisModule END getModule;

(* ==================================================== *)

  PROCEDURE SetRetAdjust(exp : BOOLEAN);
  BEGIN
    IF exp THEN retAdjust := -1 ELSE retAdjust := 0 END;
  END SetRetAdjust;

  PROCEDURE ZeroStack;
  BEGIN
    thisHeight := 0;
    maxHeight  := 0;
  END ZeroStack;

  PROCEDURE TellHeight;
  BEGIN
    BuffS("  // sh:"); 
    BuffInt(thisHeight); Comma; BuffInt(maxHeight); 
    BuffEol;
  END TellHeight;

  PROCEDURE MaxStack;
  BEGIN
    IF maxHeight <= 8 THEN BuffS("  //") ELSE BuffS("  ") END;
    BuffS(".maxstack "); BuffInt(maxHeight); BuffEol;
  END MaxStack;

  PROCEDURE Adjust(n : INTEGER);
  BEGIN
    IF n # 0 THEN
      thisHeight := thisHeight + n;
      IF thisHeight > maxHeight THEN maxHeight := thisHeight END;
    END;
  END Adjust;

(* ==================================================== *)

    PROCEDURE BuffI(val : Instruction);
    BEGIN
      IF verbose IN modState THEN TellHeight END;
      HTab; BuffS(M2IL.op[val]); HTab;
      Adjust(M2IL.dl[val]);
    END BuffI;

    PROCEDURE BuffIx(val : Instruction; adj : INTEGER);
    BEGIN
      IF verbose IN modState THEN TellHeight END;
      HTab; BuffS(M2IL.op[val]); HTab;
      Adjust(adj);
    END BuffIx;

    PROCEDURE Return;
    BEGIN
      BuffIx(opc_ret, retAdjust); BuffEol;
    END Return;

    PROCEDURE WriteByte(b : Card8);
    BEGIN
      WriteObjByte(b);
    END WriteByte;

    PROCEDURE Space();
    BEGIN
      WriteObjByte(" ");
    END Space;

    PROCEDURE Star();
    BEGIN
      WriteObjByte("*");
    END Star;

    PROCEDURE Ampersand();
    BEGIN
      BuffS("& pinned");
    END Ampersand;

    PROCEDURE Comma();
    BEGIN
      WriteObjByte(",");
    END Comma;

    PROCEDURE Dot();
    BEGIN
      WriteObjByte(".");
    END Dot;

    PROCEDURE DColon();
    BEGIN
      WriteObjByte(":");
      WriteObjByte(":");
    END DColon;

    PROCEDURE HTab();
    BEGIN
      WriteObjByte("	");
    END HTab;

    PROCEDURE LBrace();
    BEGIN
      WriteObjByte("{");
    END LBrace;

    PROCEDURE RBrace();
    BEGIN
      WriteObjByte("}");
    END RBrace;

    PROCEDURE LBrace2();
    BEGIN
      BuffS("  {");
    END LBrace2;

    PROCEDURE RBrace2();
    BEGIN
      BuffS("  }");
    END RBrace2;

    PROCEDURE BuffEol();
    BEGIN
      (*
       *  This is a version dependency caused by the
       *  fact that M2Inout writes to a binary file.
       *  THIS VERSION IS FOR UNIX, but ILASM doesn't mind.
       *)
      WriteObjByte(Ascii.lf);
    END BuffEol;

    PROCEDURE BuffCrd(c : CARDINAL);
      VAR str : StringType;
          idx : [0 .. 31];
    BEGIN
      IF c = 0 THEN WriteObjByte('0'); RETURN END;
      idx := 0;
      REPEAT
        str[idx] := CHR(c MOD 10 + ORD('0'));
        c := c DIV 10;
        INC(idx);
      UNTIL c = 0;
      FOR idx := idx - 1 TO 0 BY -1 DO 
        WriteObjByte(str[idx]);
      END;
    END BuffCrd;

    PROCEDURE BuffInt(c : INTEGER);
    BEGIN
     (* Is this safe for c = minInt  ??? *)
     (* Only if range checks are off !!! *)
(* $T- *) (* $R- *) (* $I- *)
      IF c < 0 THEN
        WriteObjByte("-");
        c := -c;
      END;
      BuffCrd(c);
(* $I= *) (* $R= *) (* $T= *)
    END BuffInt;

    PROCEDURE BuffHuge(c : HugeInts.HUGEINT);
      VAR str : StringType;
          idx : [0 .. 63];
    BEGIN
(* $T- *) (* $R- *) (* $I- *)
      IF c < 0 THEN
        WriteObjByte("-");
        c := -c;
      END;

BuffCrd(SYSTEM.CAST(CARDINAL,c));
(*
 *  This needs to be fixed when literals are internally stored as huge ints.
 *
 *    IF c = 0 THEN WriteObjByte('0'); RETURN END;
 *    idx := 0;
 *    REPEAT
 *      str[idx] := CHR(c MOD 10 + ORD('0'));
 *      c := c DIV 10;
 *      INC(idx);
 *    UNTIL c = 0;
 *    FOR idx := idx - 1 TO 0 BY -1 DO 
 *      WriteObjByte(str[idx]);
 *    END;
 *)
(* $I= *) (* $R= *) (* $T= *)
    END BuffHuge;

    PROCEDURE BuffH(n : HashBucketType);
      VAR ix,jx : CARDINAL;
          st : StringType;
    BEGIN
      ix := 0;
      GetSourceRep(n,st,ix);
      FOR jx := 0 TO ix - 1 DO WriteObjByte(st[jx]) END;
    END BuffH;

    PROCEDURE BuffN(n : HashBucketType);
      VAR ix,jx : CARDINAL;
          st : StringType;
    BEGIN
      ix := 1;
      st[0] := "'";
      GetSourceRep(n,st,ix);
      FOR jx := 0 TO ix - 1 DO WriteObjByte(st[jx]) END;
      WriteObjByte("'");
    END BuffN;

    PROCEDURE BuffS(s : ARRAY OF CHAR);
      VAR ix : CARDINAL; ch : CHAR;
    BEGIN
      FOR ix := 0 TO HIGH(s) DO
        ch := s[ix];
        IF ch = "" THEN RETURN ELSE WriteObjByte(ch) END;
      END;
    END BuffS;

    PROCEDURE QuStr(s : ARRAY OF CHAR);
    BEGIN
      WriteObjByte('"'); BuffS(s); WriteObjByte('"');
    END QuStr;

    PROCEDURE NamespaceEnd(h : HashBucketType);
    BEGIN
      BuffS("} // end of namespace ");
      BuffN(h);
      BuffEol;
    END NamespaceEnd;

    PROCEDURE NamespaceBegin(n : HashBucketType;
                             m : IdDesc);
      VAR st : StringType;
    BEGIN
      SetModule(m);
      BuffEol;
      BuffS(".namespace ");
      BuffN(n);
      BuffEol;
      WriteObjByte("{");
      BuffEol;
    END NamespaceBegin;

    PROCEDURE CommentBegin();
    BEGIN
      WriteObjByte("/");
      WriteObjByte("/");
      WriteObjByte(" ");
    END CommentBegin;

    PROCEDURE CommentEnd();
    BEGIN
      BuffEol;
    END CommentEnd;

    PROCEDURE WriteComment(s : ARRAY OF CHAR);
    BEGIN
      CommentBegin; BuffS(s); CommentEnd;
    END WriteComment;

    PROCEDURE CommentStart(s : ARRAY OF CHAR);
    BEGIN
      CommentBegin; Space; BuffS(s);
    END CommentStart;

    PROCEDURE WriteGreeting();
      CONST headr = "CIL-Code output produced by gpm from ";
    BEGIN
      WriteComment(""); 
      WriteComment("GPM-CLR version 0.2, June 07 2010"); 
      CommentBegin(); 
      EmitFileName(headr);
      WriteComment(""); 
      CommentEnd(); 
    END WriteGreeting;

    PROCEDURE WriteHeaderRecord();
    BEGIN
      BuffS(".assembly '");
      BuffS(thisName);
      BuffS("' {}");
      BuffEol;
    END WriteHeaderRecord;

  END WriteDASM;

(*====================================================*)

  MODULE JumpTables;
    IMPORT 
        Instruction, BuffI, Storage, JumpTabDesc, 
        BuffEol, Comma, HTab, BuffS, Assert, TheLabel;

    EXPORT Switch, CreateJumpTable;

    PROCEDURE CreateJumpTable(num : CARDINAL; VAR tab : JumpTabDesc);
      VAR ix : CARDINAL;
    BEGIN (* size ~ 2; locn ~ 2; elems ~ num * 2; *)
      Assert(num < 4096);
      Storage.ALLOCATE(tab, 4 + num * 2);
      tab^.size := num;
      FOR ix := 0 TO num - 1 DO
        tab^.elems[ix] := 0;
      END;
    END CreateJumpTable;

    PROCEDURE Switch(tab : JumpTabDesc);
      VAR idx : CARDINAL;
          lim : CARDINAL;
    BEGIN
      lim := tab^.size-1;
      BuffI(opc_switch); BuffS("(");
      FOR idx := 0 TO lim -1 DO
        BuffEol; HTab; HTab; TheLabel(tab^.elems[idx]); Comma;
      END;
      BuffEol; HTab; HTab; TheLabel(tab^.elems[lim]); BuffS(")"); BuffEol;
    END Switch;

  END JumpTables;

(*====================================================*)

  MODULE ClrNames;

    IMPORT (* Terminal, *) StdError, DiagName, Storage;
    IMPORT 
        HashBucketType, Spellix, pervasiveUnit, Assert,
        IdNodeClass, FormalClass, TyNodeClass, PointerTo,
        IdDesc, TypeDesc, IdTree, TyString, GetString,
        GetSourceRep, EnterString, thisCompileUnit, 
        bytesInWord, anonBkt, rtsBkt, wrapBkt, 
        IsSignedType, ListPInvoke,
        APPEND, ALLOCATE, DEALLOCATE;

    EXPORT 
        RenameStdTypes, 
        crdHsh, bytHsh, intHsh, voidStar, 
        MkStaticClrName, MkDynamicClrName, 
        MkWrapperClrName, MkPInvokeClrName,
        clrTyName, clrIdName, clrRefName,
        workList, ListPublicTypes, RenameLocalTypes;

   (* ---------------------------------------------- *)

    TYPE  Map = ARRAY [0 .. 15] OF CHAR;

    CONST max = 4095;
          hex = Map{'0','1','2','3','4','5','6','7',
                    '8','9','a','b','c','d','e','f'};

    VAR   str    : ARRAY [0 .. max] OF CHAR;
          voidStar                       : HashBucketType;
          bytHsh, u16Hsh, crdHsh         : HashBucketType;
          schHsh, i16Hsh, intHsh, i64Hsh : HashBucketType;

    VAR   workList : TyString;

   (* ---------------------------------------------- *)

    MODULE TypeSerial;
      EXPORT ResetSerialNum, serial;

      VAR   serNum : CARDINAL;

      PROCEDURE serial() : CARDINAL;
      BEGIN
        INC(serNum); RETURN serNum;
      END serial;

      PROCEDURE ResetSerialNum();
      BEGIN
        serNum := 0;
      END ResetSerialNum;

    END TypeSerial;

   (* ---------------------------------------------- *)

    PROCEDURE MkWrapperClrName(this : IdDesc); (* the current IdDesc *)
      VAR idx : CARDINAL;
    BEGIN
      idx := 0;
      GetSourceRep(thisCompileUnit^.clrName, str, idx);
      str[idx] := "."; INC(idx);
      GetSourceRep(wrapBkt, str, idx);
      str[idx] := ":"; INC(idx);
      str[idx] := ":"; INC(idx);
      str[idx] := "'"; INC(idx);
      GetSourceRep(this^.name, str, idx);    (* proc simple name   *)
      str[idx] := "'"; INC(idx);
      str[idx] := "";
      EnterString(str, this^.clrName);
    END MkWrapperClrName;

   (* ---------------------------------------------- *)

    PROCEDURE MkPInvokeClrName(this : IdDesc); (* the current IdDesc *)
      VAR idx : CARDINAL;
    BEGIN
      idx := 0;
      GetSourceRep(thisCompileUnit^.clrName, str, idx);
      str[idx] := "."; INC(idx);
      GetSourceRep(this^.module^.name, str, idx);    
      str[idx] := ":"; INC(idx);
      str[idx] := ":"; INC(idx);
      str[idx] := "'"; INC(idx);
      IF this^.extAlias # 0 THEN
        GetAsmNameFromSpix(this^.extAlias, str, idx);  (* explicit alias nam *)
      ELSE
        GetSourceRep(this^.name, str, idx);            (* proc. simple name  *)
      END;
      str[idx] := "'"; INC(idx);
      str[idx] := "";
      EnterString(str, this^.clrName);
      ListPInvoke(this);
    END MkPInvokeClrName;

   (* ---------------------------------------------- *)

    PROCEDURE MkStaticClrName(this : IdDesc;   (* the current IdDesc *)
                              pMod : IdDesc);  (* the parent module  *)
      VAR idx : CARDINAL;
    BEGIN
      idx := 0;
      GetSourceRep(pMod^.clrName, str, idx);   (* outer namespace nm *)
      str[idx] := "."; INC(idx);
      IF this^.idClass = modNode THEN
        GetSourceRep(this^.name, str, idx);    (* this module name   *)
      ELSE
        GetSourceRep(pMod^.name, str, idx);    (* dummy static class *)
        str[idx] := ":"; INC(idx);
        str[idx] := ":"; INC(idx);
        str[idx] := "'"; INC(idx);
        GetSourceRep(this^.name, str, idx);    (* proc simple name   *)
        str[idx] := "'"; INC(idx);
        str[idx] := "";
      END;
      EnterString(str, this^.clrName);
      IF this^.idClass # modNode THEN RenameLocalTypes(this, this^.scope) END;
    END MkStaticClrName;

   (* ---------------------------------------------- *)

    PROCEDURE MkDynamicClrName(this : IdDesc;   (* the current IdDesc *)
                               pMod : IdDesc;   (* enclosing module   *)
                               prnt : IdDesc);  (* the parent scope   *)
      VAR idx : CARDINAL;
    BEGIN
      idx := 0;                                 (* mangle this^.name  *)
      GetSourceRep(prnt^.name, str, idx);       (* 'outerNm.innerNm'  *)
      str[idx] := "."; INC(idx);
      GetSourceRep(this^.name, str, idx);
      EnterString(str, this^.name);             (* store dotted name  *)
      IF this^.idClass <> modNode THEN 
        idx := 0;
        GetSourceRep(pMod^.clrName, str, idx);  (* namespace string   *)
        str[idx] := "."; INC(idx);
        GetSourceRep(pMod^.name, str, idx);     (* dummy static class *)
        str[idx] := ":"; INC(idx);
        str[idx] := ":"; INC(idx);
        str[idx] := "'"; INC(idx);
        GetSourceRep(this^.name, str, idx);     (* proc dotted-name   *)
        str[idx] := "'"; INC(idx);
        str[idx] := "";
        EnterString(str, this^.clrName);
        RenameLocalTypes(this, this^.scope);
      END;
    END MkDynamicClrName;

   (* ---------------------------------------------- *)

    PROCEDURE GetAsmNameFromSpix(spx : Spellix; 
                             VAR buf : ARRAY OF CHAR; 
                             VAR jdx : CARDINAL);
      VAR kdx : CARDINAL;
          tmp : ARRAY [0 .. 511] OF CHAR;
          chr : CHAR;
    BEGIN
      GetString(spx, tmp);  (* assert: str is nul-terminated *)
      chr := tmp[0]; 
      kdx := 1;
      WHILE (chr # ".") AND (chr # "") DO
        buf[jdx] := chr; INC(jdx); 
        chr := tmp[kdx]; INC(kdx);
      END;
    END GetAsmNameFromSpix;

   (* ---------------------------------------------- *)

    PROCEDURE FixClrName(id : IdDesc);
      VAR idx : CARDINAL;
          str : ARRAY [0 .. 511] OF CHAR;
    BEGIN
      CASE id^.idClass OF
      | varNode :
          IF id^.varClass = auto THEN (* local var *)
            id^.clrName := id^.name;
          ELSIF id^.varClass = extern THEN (* imported *)
            idx := 0;
            GetSourceRep(clrRefName(id^.origMod),str,idx);
            str[idx] := "."; INC(idx);
            GetSourceRep(id^.origMod^.name,str,idx);
            str[idx] := ":"; INC(idx);
            str[idx] := ":"; INC(idx);
            str[idx] := "'"; INC(idx);
            GetSourceRep(id^.name,str,idx);
            str[idx] := "'"; INC(idx);
            str[idx] := "";
            EnterString(str, id^.clrName);
          ELSIF (id^.varClass = static) OR (id^.varClass = export) THEN
            idx := 0;
            GetSourceRep(clrRefName(id^.enclFrm),str,idx);
            str[idx] := "."; INC(idx);
            GetSourceRep(id^.enclFrm^.name,str,idx);
            str[idx] := ":"; INC(idx);
            str[idx] := ":"; INC(idx);
            str[idx] := "'"; INC(idx);
            GetSourceRep(id^.name,str,idx);
            str[idx] := "'"; INC(idx);
            str[idx] := "";
            EnterString(str, id^.clrName);
          END;
      | conProc :
          id^.clrName := clrRefName(id^.procId);
      | externProc :
          IF id^.module^.direct THEN
            MkPInvokeClrName(id);
          ELSE
            idx := 0;
            GetSourceRep(clrRefName(id^.module),str,idx);
            str[idx] := "."; INC(idx);
            GetSourceRep(id^.module^.name,str,idx);
            str[idx] := ":"; INC(idx);
            str[idx] := ":"; INC(idx);
            str[idx] := "'"; INC(idx);
            GetSourceRep(id^.name,str,idx);
            str[idx] := "'"; INC(idx);
            str[idx] := "";
            EnterString(str, id^.clrName);
          END;
      | cilWrapper :
          MkWrapperClrName(id);
      | modNode :
          IF id = thisCompileUnit THEN
            id^.clrName := id^.name;
          ELSE
            idx := 0;
            GetSourceRep(clrRefName(id^.outside), str, idx);
            str[idx] := "."; INC(idx);
            GetSourceRep(id^.name, str, idx);
            EnterString(str, id^.clrName);
          END;
      | typeNode  : id^.clrName := clrTyName(id^.typType);
      | fieldNode :
          Assert(FALSE, "fieldNode should be unreachable");
      | exportNode :  (* default case *)
          idx := 0;
          str[idx] := "["; INC(idx);
          IF id^.system THEN
            GetSourceRep(rtsBkt,str,idx);
          ELSIF NOT id^.macro OR (id^.libSpx = 0) THEN
            GetSourceRep(id^.name,str,idx);
          ELSIF NOT id^.direct THEN
            GetAsmNameFromSpix(id^.libSpx, str, idx);
          ELSE
            (* skip *)
          END;
          str[idx] := "]"; INC(idx);
          GetSourceRep(id^.name,str,idx);
          EnterString(str, id^.clrName);
      END;
    END FixClrName;

   (* ---------------------------------------------- *)

    PROCEDURE clrIdName(id : IdDesc) : HashBucketType;
    BEGIN
      WITH id^ DO
        IF clrName = anonBkt THEN FixClrName(id) END;
        RETURN name;
      END;
    END clrIdName;

   (* ---------------------------------------------- *)

    PROCEDURE clrRefName(id : IdDesc) : HashBucketType;
    BEGIN
      WITH id^ DO
        IF clrName = anonBkt THEN FixClrName(id) END;
        RETURN clrName;
      END;
    END clrRefName;

   (* ---------------------------------------------- *)

    PROCEDURE typDemand(ty : TypeDesc) : HashBucketType;
      VAR name  : ARRAY [0 .. 13] OF CHAR;
          tNum  : CARDINAL;
          equiv : HashBucketType;
     (* ---------------------------- *)
      PROCEDURE equivArray(prot : TypeDesc) : HashBucketType;
        VAR type : TypeDesc;
            indx : INTEGER;
      BEGIN
        indx := 0;
        WHILE indx <= HIGH(workList) DO
          type := workList[indx];
          IF (type^.tyClass = arrays) AND 
             (type^.size = prot^.size) THEN RETURN type^.tyName;
          ELSE INC(indx);
          END;
        END;
        RETURN anonBkt;
      END equivArray;
     (* ---------------------------- *)
    BEGIN
      WITH ty^ DO
        IF parentMod^.idClass = exportNode THEN (* imported type *)
          IF parentMod^.clrName = anonBkt THEN FixClrName(parentMod) END;
        ELSIF NOT listed THEN
          IF tyName = anonBkt THEN
            CASE tyClass OF
            | sets    : name := "Anon$SetTxxxx";
            | enums   : name := "Anon$Enumxxxx";
            | records : name := "Anon$RecTxxxx";
            | arrays  : 
                equiv := equivArray(ty);
                IF equiv # anonBkt THEN
                  tyName := equiv; 
                  listed := TRUE;
                  RETURN equiv;                      (* PREMATURE EXIT HERE! *)
                ELSE
                  name := "Anon$ArrTxxxx";
                END;
            END;
            tNum := serial();
            name[12] := hex[tNum MOD 16]; tNum := tNum DIV 16;
            name[11] := hex[tNum MOD 16]; tNum := tNum DIV 16;
            name[10] := hex[tNum MOD 16]; tNum := tNum DIV 16;
            name[ 9] := hex[tNum MOD 16]; 
            EnterString(name, tyName);
          END;
          APPEND(workList, ty);
          listed := TRUE;
        END;
        RETURN tyName;
      END;
    END typDemand;

   (* ---------------------------------------------- *)

    PROCEDURE ptrDemand(ty : TypeDesc) : HashBucketType;
      VAR indx : CARDINAL;
          tHsh : CARDINAL;
    BEGIN
      WITH ty^ DO
        IF NOT listed THEN
          IF (tyName <> anonBkt) AND (targetType^.tyName = anonBkt) THEN
            targetType^.tyName := tyName;
          END;
          indx := 0;
          tHsh := clrTyName(targetType);
          GetSourceRep(tHsh, str, indx);
          EnterString(str, tyName);
          listed := TRUE;
         (*
          *   So far as name emission goes
          *   the *originating* module is 
          *   the module of the bound type.
          *)
          parentMod := targetType^.parentMod;
        END;
        RETURN tyName;
      END;
    END ptrDemand;

   (* ---------------------------------------------- *)

    PROCEDURE clrTyName(ty : TypeDesc) : HashBucketType;
      VAR sign : BOOLEAN;
    BEGIN
      CASE ty^.tyClass OF
      | stringTs :                       RETURN anonBkt;
      | hiddens, procTypes, funcTypes :  RETURN voidStar;
      | pointers, managedRef :           RETURN ptrDemand(ty);
      | records, unions, arrays, enums : RETURN typDemand(ty);
      | opaqueTemp :                     RETURN clrTyName(ty^.resolvedType);
      | subranges : 
          sign := IsSignedType(ty^.hostType);
          ty^.parentMod := pervasiveUnit;
          CASE ty^.size OF
          | 1 : IF sign THEN RETURN schHsh ELSE RETURN bytHsh END;
          | 2 : IF sign THEN RETURN i16Hsh ELSE RETURN u16Hsh END;
          | 4 : IF sign THEN RETURN intHsh ELSE RETURN crdHsh END;
          | 8 : RETURN i64Hsh;
          END;
      | sets      : 
          IF ty^.size <= bytesInWord THEN RETURN intHsh 
          ELSE RETURN typDemand(ty);
          END;
      ELSE
        RETURN ty^.tyName;
      END;
    END clrTyName;

   (* ---------------------------------------------- *)

    PROCEDURE ListPublicTypes();
     (* -------------------------------------- *)
      PROCEDURE List(scp : IdTree); 
        VAR tId : IdDesc;
      BEGIN
        IF scp <> NIL THEN
          tId := scp^.ident;
          WITH tId^ DO
            IF (idClass = typeNode) AND
               (clrName = anonBkt) THEN
              FixClrName(tId);
            END;
          END;
          List(scp^.left); List(scp^.right); 
        END;
      END List;
     (* -------------------------------------- *)
    BEGIN
      List(thisCompileUnit^.scope);
    END ListPublicTypes;

   (* ---------------------------------------------- *)

    PROCEDURE RenameLocalTypes(id : IdDesc; sc : IdTree);
      VAR tId : IdDesc;
          hsh : HashBucketType;
          idx : CARDINAL;
    BEGIN
      IF sc <> NIL THEN
        tId := sc^.ident;
        WITH tId^ DO
          IF idClass = typeNode THEN
            idx := 0;
            hsh := tId^.typType^.tyName;
(*
DiagName(hsh); StdError.WriteString("-->");
 *)
            GetSourceRep(id^.name, str, idx);
            str[idx] := "."; INC(idx);
            GetSourceRep(hsh, str, idx);
            str[idx] := ""; INC(idx);
            EnterString(str, tId^.typType^.tyName);
(*
DiagName(tId^.typType^.tyName); StdError.WriteLn;
 *)
          END;
        END;
        RenameLocalTypes(id, sc^.left); RenameLocalTypes(id, sc^.right); 
      END;
    END RenameLocalTypes;

   (* ---------------------------------------------- *)

    PROCEDURE RenameStdTypes();
      VAR ptr : TypeDesc;
          hsh : HashBucketType;
    BEGIN
     (*
      *  Change the internal names used by GPM to
      *  the name-strings recognized by ILASM.
      *)
      EnterString("unsigned int8",  bytHsh);
      EnterString("unsigned int16", u16Hsh);
      EnterString("unsigned int32", crdHsh);

      EnterString("int8",  schHsh);
      EnterString("int16", i16Hsh);
      EnterString("int32", intHsh);
      EnterString("int64", i64Hsh);

      ptr := PointerTo(bools);
      ptr^.tyName := bytHsh;
      ptr := PointerTo(chars);
      ptr^.tyName := bytHsh;

      ptr := PointerTo(ints);
      ptr^.tyName := intHsh;
      ptr := PointerTo(words);
      ptr^.tyName := intHsh;

      ptr := PointerTo(cards);
      ptr^.tyName := crdHsh;

      ptr := PointerTo(hInts);
      ptr^.tyName    := i64Hsh;
      ptr^.parentMod := pervasiveUnit;  (* warp the parent module *)

      EnterString("float32", hsh);
      ptr := PointerTo(floats);
      ptr^.tyName := hsh;

      EnterString("float64", hsh);
      ptr := PointerTo(doubles);
      ptr^.tyName := hsh;

      EnterString("void*", voidStar);
      ptr := PointerTo(adrs);
      ptr^.tyName := voidStar;

      ptr := PointerTo(bytes);
      ptr^.tyName := schHsh;

      ResetSerialNum();
    END RenameStdTypes;

  BEGIN
    NEW(workList, 8);
  END ClrNames;

(*====================================================*)

  MODULE VectorOperations;
    IMPORT
      Assert, HTab, Comma, CatEnum, 
      BuffI, BuffIx, BuffS, BuffEol, Instruction;

    EXPORT 
      GetBlobAddress, CallVectorCtor, CallVectorDtor,
      GetVectorBlob, GetVectorHigh, PutVectorHigh, 
      GetVectorLimit, CallVectorConcat, CallVectorExpand;

    CONST
      root = "[M2ClrRts]Vector.Vector::";
      vTyp = "valuetype [M2ClrRts]Vector.Vec::";
      vPtr = "valuetype [M2ClrRts]Vector.Vec* ";

    PROCEDURE CallVectorExpand();
    BEGIN
      BuffIx(opc_call, -2); BuffS("void "); BuffS(root);
      BuffS("Expand(valuetype [M2ClrRts]Vector.Vec*,int32)"); BuffEol;
    END CallVectorExpand;

    PROCEDURE CallVectorDtor();
    BEGIN
      BuffIx(opc_call, -1); BuffS("void "); BuffS(root);
      BuffS("'Dispose'(valuetype [M2ClrRts]Vector.Vec*)"); BuffEol;
    END CallVectorDtor;

    PROCEDURE CallVectorCtor();
    BEGIN
      BuffIx(opc_call, -1); BuffS(vPtr); BuffS(root);
      BuffS("newVector(int32, int32)"); BuffEol;
    END CallVectorCtor;

    PROCEDURE GetVectorBlob();
    (* reference to vector is on eval stack *)
    BEGIN
      BuffI(opc_ldfld); 
      BuffS("unsigned int8* "); BuffS(vTyp); BuffS("'blob'"); BuffEol;
    END GetVectorBlob;

    PROCEDURE GetBlobAddress();
    (* reference to vector is on eval stack *)
    BEGIN
      BuffI(opc_ldflda); 
      BuffS("unsigned int8* "); BuffS(vTyp); BuffS("'blob'"); BuffEol;
    END GetBlobAddress;

    PROCEDURE GetVectorHigh();
    (* reference to vector is on eval stack *)
    BEGIN
      BuffI(opc_ldfld); 
      BuffS("int32 "); BuffS(vTyp); BuffS("'high'"); BuffEol;
    END GetVectorHigh;

    PROCEDURE PutVectorHigh();
    (* stack is ... vector ref, new high value *)
    BEGIN
      BuffI(opc_stfld); 
      BuffS("int32 "); BuffS(vTyp); BuffS("'high'"); BuffEol;
    END PutVectorHigh;

    PROCEDURE GetVectorLimit();
    (* reference to vector is on eval stack *)
    BEGIN
      BuffI(opc_ldfld); 
      BuffS("int32 "); BuffS(vTyp); BuffS("'elNm'"); BuffEol;
    END GetVectorLimit;

    PROCEDURE CallVectorConcat(n : CatEnum);
    BEGIN
      CASE n OF
      | stCat : (* stack: ... &mVec, &vec2     *) 
          BuffIx(opc_call, -2); BuffS("void "); BuffS(root);
          BuffS("CatVec("); BuffEol;
          HTab; HTab; BuffS(vPtr); Comma; BuffS(vPtr); BuffS(")"); 
      | ssCat : (* stack: ... &mVec, &str, sHi *)
          BuffIx(opc_call, -3); BuffS("void "); BuffS(root);
          BuffS("CatArr("); BuffEol;
          HTab; HTab; BuffS(vPtr); BuffS(",unsigned int8*, unsigned int32)");
      | chCat : (* stack: ... &mVec, chr       *)
          BuffIx(opc_call, -2); BuffS("void "); BuffS(root);
          BuffS("CatChr("); BuffEol;
          HTab; HTab; BuffS(vPtr); BuffS(",unsigned int8)");
      END;
      BuffEol;
    END CallVectorConcat;

  END VectorOperations;

(*====================================================*)

  MODULE LitChainDump;
  IMPORT StdError;
  IMPORT BuffS, BuffEol, Space, HTab, thisName;

  IMPORT LabelType, AllocLabel, HashBucketType, FP_Overflow,
         chainTail, chainHead, thisCompileUnit, 
         ExprDesc, ExprRec, bytesInReal, bytesInWord, WriteComment,
         IdDesc, TypeDesc, LexAttType, ExprNodeClass, GetSourceRep,
         EnterString, StrucTree, StringType, bigEndian, crossEndian,
         ConBlock, TyNodeClass, Assert, StringTable, INFINITY, Card32;

  IMPORT WriteObjByte;

  EXPORT EmitLitChain;

  (*
   *  this code is endian independent of the host machine
   *)

    TYPE  Map  = ARRAY [0 .. 15] OF CHAR;
    CONST map1 = Map{" ","1","2","3","4","5","6","7",
                     "8","9","A","B","C","D","E","F"};
          map2 = Map{"0","1","2","3","4","5","6","7",
                     "8","9","A","B","C","D","E","F"};

    VAR  num, total  : CARDINAL;
         end : ARRAY [0 .. 17] OF CHAR;

    PROCEDURE SpillAscii;
      VAR ix : CARDINAL;
    BEGIN
      IF num <> 0 THEN
        FOR ix := 1 TO (16 - num) DO BuffS("   ") END;
        end[num] := "]";
        end[num + 1] := "";
        BuffS(" //["); BuffS(end);
      END;
    END SpillAscii;

    PROCEDURE Spill(ch : CHAR);
    BEGIN
      IF num = 0 THEN HTab ELSE Space END;
      IF (ch>=" ") AND (ch<177C) THEN end[num] := ch ELSE end[num] := "." END;
      WriteObjByte(map1[ORD(ch) DIV 16]);
      WriteObjByte(map2[ORD(ch) MOD 16]);
      INC(num); INC(total);
      IF num = 16 THEN 
        SpillAscii;
        BuffEol; num := 0;
      END;
    END Spill;

    PROCEDURE DumpLitExpr(ptr : ExprDesc);
      TYPE Bytes = ARRAY [0 .. 3] OF CHAR;
      VAR  spix, ix : CARDINAL;
           index    : CARDINAL;
           ch       : CHAR;
           vPtr     : ConBlock;
           lTyp     : TypeDesc;
           lVal     : LexAttType;
           short    : RECORD CASE : INTEGER OF
        		| 0 : flt   : SHORTREAL;
        		| 1 : card  : Card32;
        		| 2 : bytes : Bytes;
        	      END END;
    BEGIN
      IF ptr^.exprClass = selConstNode THEN
        lTyp := ptr^.name.variable^.conType;
        lVal := ptr^.name.variable^.conValue;
      ELSE
        lTyp := ptr^.exprType;
        lVal := ptr^.conValue;
      END;
      IF lTyp^.tyClass = sets THEN
        Assert(total <= ptr^.rtOffset);
        WHILE total < ptr^.rtOffset DO Spill(0C) END;
        spix := lVal.patternIx;
        ix := 0;
        WHILE ix < lTyp^.size DO			(* jl Jun 94 *)
          (* must emit in target endian style *)
          IF bigEndian <> crossEndian THEN (* big endian *)
            FOR index := spix + bytesInWord - 1 TO spix BY -1 DO
              Spill(StringTable(index));
            END;
          ELSE (* little endian *)
            FOR index := spix TO spix + bytesInWord - 1 DO
              Spill(StringTable(index));
            END;
          END;
          INC(ix,bytesInWord); INC(spix,bytesInWord);
        END;
      ELSIF (lTyp^.tyClass = SS) THEN (* is string *)
 	Assert(total = ptr^.rtOffset);
        IF lVal.stringIx = 0 THEN (* charNum being coerced *);
          (*
           *  changes for charNums 12-Jun-90
           *  needed in order to add string concatenation
           *)
          ch := lVal.charValue;
          Spill(ch); Spill(0C);
        ELSE
          FOR spix := lVal.stringIx TO lVal.stringIx + lVal.strHigh DO
 	    Spill(StringTable(spix));
          END;
        END;
      ELSIF (lTyp^.tyClass = RR) THEN (* is real *)
        Assert(total <= ptr^.rtOffset);
        WHILE total < ptr^.rtOffset DO Spill(0C) END;
        FP_Overflow := (lVal.floatValue = INFINITY) OR
        	       (lVal.floatValue = -INFINITY);
        IF NOT FP_Overflow THEN short.flt := SFLOAT(lVal.floatValue) END;
        IF FP_Overflow THEN		(* Alpha dumps junk otherwise *)
          IF lVal.floatValue = -INFINITY THEN	(* if SFLOAT overflows*)
            short.card := 0FF800000H;		(* jl Jun 94 & Oct 95 *)
          ELSE
            short.card := 07F800000H;
          END;
        END;
        IF crossEndian THEN
          FOR ix := bytesInReal - 1 TO 0 BY -1 DO
            Spill(lVal.bytes[ix]);
          END;
          FOR ix := 3 TO 0 BY -1 DO
            Spill(short.bytes[ix])
          END;
        ELSE
          FOR ix := 0 TO bytesInReal - 1 DO
            Spill(lVal.bytes[ix]);
          END;
          FOR ix := 0 TO 3 DO
            Spill(short.bytes[ix])
          END;
        END;
      ELSE
        Assert(total <= ptr^.rtOffset);
        WHILE total < ptr^.rtOffset DO Spill(0C) END;
        vPtr := lVal.adrsValue;
        FOR ix := 0 TO lTyp^.size - 1 DO
          Spill(vPtr^[ix]);
        END;
      END;
    END DumpLitExpr; 

    PROCEDURE EmitLitChain();
      VAR ptr : ExprDesc;
          i   : CARDINAL;
    BEGIN
      num := 0; total := 0;

      BuffS(".field public static void* 'm$Nam' at 'm$Nam$Ptr'"); BuffEol;
      BuffS(".data 'm$Nam$Ptr' = {&('m$Nam$Dat')}");  BuffEol;
      BuffS(".data 'm$Nam$Dat' = { bytearray ("); BuffEol;
      i := 0;
      WHILE thisName[i] # "" DO Spill(thisName[i]); INC(i) END;
      Spill(0C); SpillAscii; BuffEol;
      BuffS(") }"); BuffEol; BuffEol;

     (* now the literal chain (if not empty) is added *)
      IF chainHead <> NIL THEN
        num := 0; total := 0;
        BuffS(".field public static void* 'c$Dat' at 'c$Dat$Ptr'"); BuffEol;
        BuffS(".data 'c$Dat$Ptr' = {&('c$Dat$Dat')}");  BuffEol;
        BuffS(".data 'c$Dat$Dat' = { bytearray ("); BuffEol;
        ptr := chainHead;
        LOOP
          DumpLitExpr(ptr);
          IF ptr = chainTail THEN EXIT END;
          ptr := ptr^.chainLnk;
        END;
        SpillAscii;   BuffEol;
        BuffS(") } "); WriteComment("End of constant pool");
      END;
      BuffEol;
    END EmitLitChain;

  END LitChainDump;

(*====================================================*)
(*====================================================*)

  MODULE PInvokeDefinitions;

    IMPORT IdString, IdDesc,
           ClassBegin, ClassEnd, EmitPInvoke,
           ALLOCATE, DEALLOCATE, APPEND, CUT;

    EXPORT pInvList, ListPInvoke, DoPInvokeImpls;

    VAR pInvList : IdString;
        iModList : IdString;

    PROCEDURE ListPInvoke(id : IdDesc);
      VAR i : INTEGER;
    BEGIN
      APPEND(pInvList, id);
      FOR i := 0 TO HIGH(iModList) DO
        IF iModList[i] = id^.module THEN RETURN END;
      END;
      APPEND(iModList, id^.module);
    END ListPInvoke;

    PROCEDURE DoPInvokeImpls;
      VAR mIx, fIx : INTEGER;
          mod, fun : IdDesc;
    BEGIN
      FOR mIx := 0 TO HIGH(iModList) DO
        mod := iModList[mIx];
       (*
        *  Emit the module class
        *)
        ClassBegin(mod^.name);
        FOR fIx := 0 TO HIGH(pInvList) DO
          fun := pInvList[fIx];
          IF fun^.module = mod THEN
           (*
            *  Emit the pinvokeimpl
            *)
            EmitPInvoke(mod, fun);
          END;
        END;
        ClassEnd(mod^.name);
      END;
    END DoPInvokeImpls;

  BEGIN
    NEW(iModList, 2);
    NEW(pInvList, 8);
  END PInvokeDefinitions;

(*====================================================*)
(*====================================================*)

  MODULE ClassDefinitions;
    IMPORT 
        SYSTEM, Assert, StdError, DiagName, debugOn, 
        workList, EmitTypeSig, EmitFrmTypeSig, PubEnum,
        InitCursor, ElemPtr, Ended, GetNext,
        BuffS, BuffH, BuffN, BuffEol, HTab, BuffCrd, 
        BuffInt, BuffIx, WriteObjByte, Space, PushInt,
        IdDesc, TypeDesc, TyNodeClass, IsStringType;

    EXPORT EmitClassDefs;

   (* ---------------------------------------------- *)

    PROCEDURE EmitEnum(ty : TypeDesc);
     (* ------------------------------------------ *)
      PROCEDURE EmitConst(id : IdDesc; pb : PubEnum);
      BEGIN
        BuffS("  .field ");
        IF pb <> notPub THEN BuffS("public ") ELSE BuffS("assembly ") END;
        BuffS("static literal "); BuffEol; HTab; HTab;
        EmitTypeSig(id^.conType); Space;
        BuffN(id^.name); 
        BuffS(" = int16(");     (* ILASM barfs on "unsigned int8" *)
        BuffCrd(id^.conValue.fixValue);
        WriteObjByte(")");
      END EmitConst;
     (* ------------------------------------------ *)
      VAR pblic : PubEnum;
          eCurs : ElemPtr;
          eElem : IdDesc;
    BEGIN
      pblic := ty^.pubTag;
      BuffS("  .class ");
      IF pblic > notPub THEN BuffS("public ") END; (* else assembly ... *)
      BuffS("value sealed ");
      BuffN(ty^.tyName); 
      BuffEol; HTab;
      BuffS("extends [mscorlib]System.Enum {"); BuffEol;
      BuffS("  .field ");
      IF pblic <> notPub THEN BuffS("public ") ELSE BuffS("assembly ") END;
      BuffS("specialname rtspecialname unsigned int8 value__"); BuffEol;
     (*
      *  Now we emit all of the fields of the record with offsets.
      *)
      InitCursor(ty^.conSeq, eCurs);
      WHILE NOT Ended(eCurs) DO
        GetNext(eCurs, eElem);
        EmitConst(eElem, pblic); BuffEol;
      END;
      BuffS("  }"); BuffEol;
    END EmitEnum;

   (* ---------------------------------------------- *)

    PROCEDURE EmitArray(ty : TypeDesc);
      VAR pblic : PubEnum;
    BEGIN
      pblic := ty^.pubTag;
      BuffS("  .class ");
      IF pblic > notPub THEN BuffS("public ") END; (* else assembly ... *)
      BuffS("explicit value sealed ");
      BuffN(ty^.tyName); 
      BuffEol; HTab;
      BuffS("extends [mscorlib]System.ValueType { .pack 1 .size "); 
      BuffCrd(ty^.size);
      IF debugOn AND IsStringType(ty) THEN BuffEol; EmitToStringMethod(ty^.size) END;
      BuffS("  }"); BuffEol;
    END EmitArray;

   (* ---------------------------------------------- *)

    PROCEDURE EmitToStringMethod(size : CARDINAL);
    BEGIN
      HTab;
      BuffS(".method public virtual instance string ToString() cil managed"); BuffEol;
      BuffS("  {"); BuffEol;
      BuffS("  .maxstack 8"); BuffEol;
      HTab; BuffS("ldarg.0"); BuffEol;
      PushInt(SYSTEM.CAST(INTEGER, size));
      HTab; BuffS("call string [M2ClrRts]Helper::BytePtrToString(uint8*, uint32)"); BuffEol;
      HTab; BuffS("ret"); BuffEol;
      BuffS("  }"); BuffEol;
    END EmitToStringMethod;

   (* ---------------------------------------------- *)

    PROCEDURE EmitField(id : IdDesc; pb : PubEnum);
      VAR vCurs : ElemPtr;
          fCurs : ElemPtr;
          vElem : TypeDesc;
          fElem : IdDesc;
          index : CARDINAL;
    BEGIN
      IF id^.fieldType^.tyClass <> unions THEN
        BuffS("    .field [");
        BuffCrd(id^.fieldOffset);
        IF pb <> notPub THEN BuffS("] public ") ELSE BuffS("] assembly ") END;
        EmitFrmTypeSig(id^.fieldType);
        WriteObjByte(" ");
        BuffN(id^.name); BuffEol;
      ELSE (* is a variant sub-record *)
        InitCursor(id^.fieldType^.varSeq, vCurs);
        WHILE NOT Ended(vCurs) DO
          GetNext(vCurs, vElem); (* variant element *)
          InitCursor(vElem^.fieldSeq, fCurs);
          WHILE NOT Ended(fCurs) DO
            GetNext(fCurs, fElem); (* field element *)
            EmitField(fElem, pb);
          END;
        END;
      END;
    END EmitField;

    PROCEDURE EmitRecord(ty : TypeDesc);
      VAR eCurs : ElemPtr;
          iElem : IdDesc;
          index : CARDINAL;
          pblic : PubEnum;
    BEGIN
      pblic := ty^.pubTag;
      BuffS("  .class ");
      IF pblic > notPub THEN BuffS("public ") END; (* else assembly ... *)
      BuffS("explicit value sealed ");
      BuffN(ty^.tyName); 
      BuffEol; HTab;
      BuffS("extends [mscorlib]System.ValueType {"); BuffEol;
     (*
      *  Now we emit all of the fields of the record with offsets.
      *)
      InitCursor(ty^.fieldSeq, eCurs);
      WHILE NOT Ended(eCurs) DO
        GetNext(eCurs, iElem);
        EmitField(iElem, pblic);
      END;
      BuffS("  }"); BuffEol;
    END EmitRecord;

   (* ---------------------------------------------- *)

    PROCEDURE EmitClassDefs();
      VAR indx : INTEGER;
          tyDx : TypeDesc;
    BEGIN
      indx := 0;
      BuffS("// emitting <"); BuffInt(HIGH(workList)+1); 
      BuffS("> local classes "); BuffEol;
      WHILE indx <= HIGH(workList) DO
        tyDx := workList[indx];
        BuffS("// emit local class "); BuffN(tyDx^.tyName); BuffEol; 
        CASE tyDx^.tyClass OF
        | sets    : EmitArray(tyDx);
        | enums   : EmitEnum(tyDx);
        | arrays  : EmitArray(tyDx);
        | records : EmitRecord(tyDx);
        END;
        BuffEol;
        INC(indx);
      END;
    END EmitClassDefs;

   (* ---------------------------------------------- *)

  END ClassDefinitions;

(*====================================================*)
(*====================================================*)

  PROCEDURE mappedToBuiltin(typ : TypeDesc) : BOOLEAN;
  BEGIN
    CASE typ^.tyClass OF
    | sets :
        RETURN typ^.size = bytesInWord;
    | opaqueTemp :
        RETURN mappedToBuiltin(typ^.resolvedType);
    | pointers, managedRef :
        RETURN mappedToBuiltin(typ^.targetType);
    | subranges, hiddens, bytes, words, adrs, procTypes, funcTypes :
        RETURN TRUE;
    ELSE
        RETURN FALSE;
    END;
  END mappedToBuiltin;

(*====================================================*)

  PROCEDURE hasClassImpl(typ : TypeDesc) : BOOLEAN;
    VAR tCls : TyNodeClass;
  BEGIN
    IF typ = NIL THEN RETURN FALSE END;
    CASE typ^.tyClass OF
    | sets :
        RETURN typ^.size > bytesInWord;
    | opaqueTemp :
        RETURN hasClassImpl(typ^.resolvedType);
    | pointers, managedRef :
        RETURN hasClassImpl(typ^.targetType);
    | records, arrays, enums :
        RETURN TRUE;
    ELSE
        RETURN FALSE;
    END;
  END hasClassImpl;

(*====================================================*)

  PROCEDURE lexLevel(id : IdDesc) : CARDINAL;
    VAR count : CARDINAL;
  BEGIN
    count := 0;
    LOOP
      CASE id^.idClass OF
        | externProc :                     RETURN 1;
        | modNode :
            IF id = thisCompileUnit THEN   RETURN count;
            ELSE 
              id := id^.outside; (* no inc *)
            END;
        | procHeader, procNode, cilWrapper :
            INC(count);
            id := id^.uphill;
        | exportNode :
            id := id^.outside; (* no inc *)
      END;
    END;
  END lexLevel;

  PROCEDURE enclosingFrame(id : IdDesc) : IdDesc;
  BEGIN
    Assert(id^.idClass IN allProcs);
    id := id^.uphill;
    WHILE id^.idClass = modNode DO id := id^.outside END;
    RETURN id;
  END enclosingFrame;

(*====================================================*)

  PROCEDURE inXSR(id : IdDesc) : BOOLEAN;
  BEGIN
    RETURN (id # NIL) AND (uplevAcc IN id^.varUseSet);
  END inXSR;

  PROCEDURE hasXSR(id : IdDesc) : BOOLEAN;
  BEGIN
    RETURN (id^.idClass # modNode) AND (id^.body # NIL) AND
                               (hasUplevObj IN id^.body^.callAttrib);
  END hasXSR;

(*====================================================*)

  (* Push static link to CALL procedure id *)
  PROCEDURE PushStaticLink(id : IdDesc);
    VAR myL : CARDINAL;
        idL : CARDINAL;
        jdx : CARDINAL;
        slf : IdDesc;
  BEGIN
    idL := lexLevel(id);
    IF idL > 1 THEN  (* need to pass static link *)
      slf := current();
      myL := lexLevel(slf);
      IF    myL = idL THEN (* share static link  *)
        BuffI(opc_ldarg_0);
        HTab; BuffS("// link from "); BuffN(slf^.name);
      ELSIF idL > myL THEN (* calling child proc *)
        IF hasXSR(slf) THEN
          PushLocalAdr(0);
          HTab; BuffS("// link toXSR "); BuffN(slf^.name);
        ELSIF myL = 1 THEN
          BuffI(opc_ldnull);
          HTab; BuffS("// null link");
        ELSE
          BuffI(opc_ldarg_0);
          slf := enclosingFrame(slf);
          HTab; BuffS("// link from "); BuffN(slf^.name);
        END;
      ELSE  (* calling relatively global proc    *)
        BuffI(opc_ldarg_0);
        HTab;
        slf := enclosingFrame(slf); DEC(myL);
        WHILE myL >= idL DO
          IF hasXSR(slf) THEN
            BuffS("// link to XSR "); BuffN(slf^.name); BuffEol;
            BuffI(opc_ldind_i4);
          END;
          slf := enclosingFrame(slf); DEC(myL);
        END;
        BuffS("// link from "); BuffN(slf^.name);
      END;
      BuffEol;
    END;
  END PushStaticLink;

(*====================================================*)

  (* Push address of uplevel datum *)
  PROCEDURE PushDataLink(id : IdDesc);
    VAR myL : CARDINAL;
        idL : CARDINAL;
        jdx : CARDINAL;
        slf : IdDesc;
  BEGIN
    slf := current();
    myL := lexLevel(slf);
    idL := lexLevel(id^.decFrame^.frame);
    IF verbose IN modState THEN 
      BuffS("// Currently at lex-level "); BuffCrd(myL); BuffEol;
      BuffS("// Push Address of XSR at lex-level "); BuffCrd(idL); 
      BuffS(", field-offset "); BuffInt(id^.varOffset); 
      BuffEol;
    END;
    BuffI(opc_ldarg_0); 
    slf := enclosingFrame(slf); DEC(myL);
   (*
    *  The incoming static link has been pushed,
    *  the target frame is the caller of current().
    *)
    WHILE myL > idL DO
      IF hasXSR(slf) THEN 
        BuffS("// link to XSR "); BuffN(slf^.name); BuffEol;
        BuffI(opc_ldind_i4); 
      END;
      slf := enclosingFrame(slf); DEC(myL);
    END;
    BuffS("// link from "); BuffN(slf^.name); 
    IF hasXSR(slf) THEN BuffS(" (has XSR)") END;
    BuffEol;
   (*
    *  And now, to prove that we are not crazy ...
    Assert(hasXSR(slf));
    *)
  END PushDataLink;

(*====================================================*)
(*====================================================*)

  PROCEDURE InitNames;
    VAR index : CARDINAL;
  BEGIN
    index := 0;
    GetSourceRep(thisCompileUnit^.name, thisName, index);
    EnterString(RTSname, rtsBkt);
    EnterString("c$Dat",conDatB);
    EnterString("m$Nam",modNamB);
    EnterString("s$Ptr",sPtrBkt);
    EnterString("$Wrap$",wrapBkt);
    EnterString(".CatchWrapper",catchBkt);
    EnterString(".cctor",cctorBkt);
    hiType := PointerTo(cards);
  END InitNames;
    
  PROCEDURE DoObjHeader(modName : HashBucketType);
  BEGIN
    InitNames;
    MakeAllClrNames(thisCompileUnit);
    RenameStdTypes();
    ListPublicTypes();
    WriteGreeting();
    WriteImports();
    WriteHeaderRecord();
  END DoObjHeader;

  PROCEDURE DoObjEnd;
  BEGIN
    WriteComment("End of gpm output");
  END DoObjEnd;

(* =============================================================== *)

  PROCEDURE EmitFieldAttr(fId : IdDesc);
  BEGIN
    WITH fId^ DO
      IF varClass = export THEN
        BuffS("public static ");
      ELSIF varClass = static THEN
        BuffS("assembly static ");
      END;
    END;
  END EmitFieldAttr;

(*====================================================*)

  PROCEDURE isVector(typ : TypeDesc) : BOOLEAN;
  BEGIN
    CASE typ^.tyClass OF
    | stringTs :             RETURN TRUE;
    | pointers, managedRef : RETURN isVector(typ^.targetType);
    ELSE                     RETURN FALSE;
    END;
  END isVector;

  PROCEDURE EmitFrmTypeSig(typ : TypeDesc);
  BEGIN
    IF typ^.pubTag = opaqueAlias THEN BuffH(voidStar); 
    ELSE EmitTypeSig(typ);
    END;
  END EmitFrmTypeSig;

  PROCEDURE EmitTypeSig(typ : TypeDesc);
    VAR hsh    : HashBucketType;
        parent : IdDesc;
   
  BEGIN
    IF isVector(typ) THEN 
      BuffS("valuetype [M2ClrRts]Vector.Vec* ");
    ELSE
      hsh := clrTyName(typ);
      IF hasClassImpl(typ) THEN BuffS("valuetype ") END;
     (*
      *   Emit type prefix
      *)
      parent := typ^.parentMod;
      IF (parent <> pervasiveUnit) AND NOT mappedToBuiltin(typ) THEN
        BuffH(parent^.clrName); Dot;
        BuffN(hsh);                (* single quotes if not pervasive id *)
      ELSE
        BuffH(hsh);                (* no quotes if not pervasive ident  *)
      END;
    END;
   (*
    *   Emit type suffix
    *)
    IF typ^.tyClass = pointers THEN Star;
    ELSIF typ^.tyClass = managedRef THEN Ampersand;
    END;
  END EmitTypeSig;

(*====================================================*)

  PROCEDURE cilEqFrm(lFrm, rFrm : FormalType) : BOOLEAN;
  BEGIN
   (*
    *  Exclude some hopeless cases ...
    *)
    IF (lFrm^.form <> rFrm^.form) OR
      ((lFrm^.form >= openValForm) AND
       (lFrm^.dimN <> rFrm^.dimN)) THEN RETURN FALSE;
    END;
   (*
    *  Now check if the formal types are compatible.
    *)
    RETURN cilEqTyp(lFrm^.type, rFrm^.type);
  END cilEqFrm;

(*====================================================*
 *  The intent here is to check if the two types have
 *  the same representation in the signatures of methods.
 *  Note that type equivalence in the M2 sense is wrong
 *  since (for example) all opaques appear as "void*".
 *  Another plausible scheme that does not work is to
 *  check if clrTyNames of the two types are equal. 
 *  In this case the names for the built-in types have 
 *  not yet been initialized when this predicate is 
 *  called from TraverseExp.
 *====================================================*)
  PROCEDURE cilEqTyp(lTyp, rTyp : TypeDesc) : BOOLEAN;
    CONST voidTs = TyClassSet{hiddens, procTypes, funcTypes, opaqueTemp};
  BEGIN
    IF lTyp = rTyp THEN 
      RETURN TRUE;
    ELSIF (lTyp = NIL) OR (rTyp = NIL) THEN 
      RETURN FALSE;
    ELSIF ((lTyp^.tyClass = stringTs) AND 
           (rTyp^.tyClass = stringTs)) OR
          ((lTyp^.pubTag = opaqueAlias) AND 
           (rTyp^.pubTag = opaqueAlias)) OR
          ((lTyp^.tyClass IN voidTs) AND 
           (rTyp^.tyClass IN voidTs)) THEN 
      RETURN TRUE;
    ELSIF (lTyp^.tyClass = pointers) AND
          (rTyp^.tyClass = pointers) THEN 
      RETURN cilEqTyp(lTyp^.targetType, rTyp^.targetType);
    ELSIF (lTyp^.tyClass = subranges) AND
          (rTyp^.tyClass = subranges) THEN 
      RETURN (lTyp^.size = rTyp^.size) AND
             (IsSignedType(lTyp^.hostType) = IsSignedType(rTyp^.hostType));
    ELSIF (lTyp^.tyClass = sets) AND
          (rTyp^.tyClass = sets) THEN 
      RETURN (lTyp^.size <= bytesInWord) = (rTyp^.size <= bytesInWord);
    END;
    RETURN FALSE;
  END cilEqTyp;

(*====================================================*)

  PROCEDURE WriteAsmNameFromSpix(spx : Spellix;
                                 trm : BOOLEAN;
                                 quo : CHAR);
    VAR chr : CHAR;
        idx : CARDINAL;      (* character index    *)
        dot : CARDINAL;      (* last '.' character *)
        str : ARRAY [0 .. 255] OF CHAR;
  BEGIN
    GetString(spx, str);  (* assert: str is nul-terminated *)
    IF trm THEN
      idx := 0; dot := 255; chr := str[0]; 
      WHILE chr <> "" DO 
        IF chr = "." THEN dot := idx END;
        INC(idx);
        chr := str[idx];
      END;
      str[dot] := ""; 
    END;
    WriteObjByte(quo);
    BuffS(str);
    WriteObjByte(quo);
  END WriteAsmNameFromSpix;

(*====================================================*)

  PROCEDURE WriteImports();
   (* ---------------------------------------------- *
    * ---------------------------------------------- *
    *      Notes on foreign language interface       *
    * ---------------------------------------------- *
    * ---------------------------------------------- *
    *  There are two attributes of imported modules. *
    *  Modules may be marked with the "macro" Bool,  *
    *  or with the "macro" AND the "direct" Boolean. *
    *  All with the macro Boolean do not have a      *
    *  corresponding *.mod file.  The treatment is   *
    *  different for those with and without the      *
    *  direct flag set.                              *
    * ---------------------------------------------- *
    *  CASE: macro AND NOT direct ==>                *
    *  implementation code is found in a CLR library *
    *  the name of which is in the libSpix string.   *
    *  The usual name mangling/namespace conventions *
    *  hold in this case.  The library is probably   *
    *  written in C#.                                *
    *  In this case libSpix may hold "file.dll".     *
    * ---------------------------------------------- *
    *  CASE: macro AND direct ==>                    *
    *  implementation code is found in a non-CLR dll *
    *  which is accessed via pinvoke calls. There is *
    *  no name-mangling, and no passing of HIGH      *
    *  values to open array parameters.              *
    *  In this case libSpix will hold "libname.dll"  *
    * ---------------------------------------------- *
    * ---------------------------------------------- *)
    VAR curs : ElemPtr;
        elem : IdDesc;
  BEGIN
    BuffS(".assembly extern mscorlib {}");
    BuffEol;

    BuffS(".assembly extern ");
    BuffN(rtsBkt);
    BuffS(" {}");
    BuffEol;

    InitCursor(globalModList,curs);
    WHILE NOT Ended(curs) DO
      GetNext(curs,elem);
      (* Assert(elem^.idClass = exportNode); *)
      IF elem^.loaded THEN
        IF elem^.system THEN
          BuffS("// System module '"); BuffH(elem^.name);
          BuffS("' from assembly ["); BuffS(RTSname); BuffS(']'); BuffEol;
        ELSIF elem^.name = thisCompileUnit^.name THEN (* skip *)
        ELSIF NOT elem^.macro OR (elem^.libSpx = 0) THEN
          BuffS(".assembly extern ");
          BuffN(elem^.name);
          BuffS(" {} // name");
          BuffEol;
        ELSIF NOT elem^.direct THEN
          BuffS(".assembly extern ");
          WriteAsmNameFromSpix(elem^.libSpx, TRUE, "'");
          BuffS(" {} // spix");
          BuffEol;
        ELSE (* direct AND macro *)
          BuffS("// Module '");
          BuffH(elem^.name);
          BuffS("' accessed via PInvoke from "); 
          WriteAsmNameFromSpix(elem^.libSpx, FALSE, '"');
          BuffEol;
        END;
      END;
    END;
    BuffEol;
  END WriteImports;

(*====================================================*)

  PROCEDURE EmitMyVars(mod : IdDesc; scp : IdTree); 
    VAR nam : HashBucketType;
        idx : CARDINAL;
        siz : CARDINAL;
        vId : IdDesc;
  BEGIN
    IF scp <> NIL THEN
      vId := scp^.ident;
      WITH vId^ DO
        IF  (idClass = varNode) AND
            (enclFrm = mod)     AND
            (varType^.size > 0) AND
            ((varClass = static) OR (varClass = export)) THEN 
          idx := 0;
          BuffS(".field ");
          EmitFieldAttr(vId);
          EmitTypeSig(vId^.varType); Space;
          BuffN(clrIdName(vId));
          BuffEol;
          BuffS("// Reference name is "); BuffH(clrRefName(vId)); BuffEol;
          WriteComment("");
          BuffEol;
        END;
      END;
      EmitMyVars(mod, scp^.left); EmitMyVars(mod, scp^.right);
    END;
  END EmitMyVars;

(*====================================================*)

  PROCEDURE MakeAllClrNames(root : IdDesc);
   (* ---------------------------------------------- *
    *   Notes on name translation:
    *   Static modules have nested names, so
    * ---------------------------------------------- *
    *   Modula-2           name          clrName
    * ---------------------------------------------- *
    *   IMPL MOD A;        'A'           A
    *     VAR a;           'a'           A.A::'a'
    *     MOD B;           'B'           A.B
    *       VAR b;         'b'           A.B.B::'b'
    *       PROC p         'p'           A.B.B::'p'
    *         PROC q       'p.q'         A.B.B::'p.q'
    * ---------------------------------------------- *
    *   In order to construct this conveniently, we
    *   need to know the identity of the "parent",
    *   the name of the enclosing namespace, and 
    *   the name of the enclosing static class.
    * ---------------------------------------------- *
    * ---------------------------------------------- *
    *   For dynamic modules the pattern is different
    *   since there is no namespace for the module.
    *   The body of the module is inlined, so the
    *   "Clr-Name" can never be used.
    * ---------------------------------------------- *
    *   PROC p;             'p'          X.X::'p'
    *     MODULE N;         'N'          X.X
    *       VAR n;          'N.n'        local 'N.n'
    *       PROC q;         'p.N.q'      X.X::'p.N.q'
    * ---------------------------------------------- *)
   (* ---------------------------------------------- *)
   (* Names for blocks with auto data, such as procs *)
   (* and modules nested inside procedures.          *)
   (* ---------------------------------------------- *)
    PROCEDURE MkDynamicChildNames(prnt,pMod : IdDesc);
      VAR str : IdString;
          idx : INTEGER;
          kid : IdDesc;
    BEGIN
      str := prnt^.body^.nestBlks;
      FOR idx := 0 TO HIGH(str) DO
        kid := str[idx];
        MkDynamicClrName(kid, pMod, prnt);
        MkDynamicChildNames(kid, pMod);
      END;
    END MkDynamicChildNames;
   (* ---------------------------------------------- *)
   (* Names for blocks with static data, such as     *)
   (* modules not nested within procedures           *)
   (* ---------------------------------------------- *)
    PROCEDURE MkStaticChildNames(pMod : IdDesc);
      VAR str : IdString;
          idx : INTEGER;
          kid : IdDesc;
    BEGIN
      str := pMod^.body^.nestBlks;
      FOR idx := 0 TO HIGH(str) DO
        kid := str[idx];
        MkStaticClrName(kid, pMod);
        IF kid^.idClass = modNode THEN
          MkStaticChildNames(kid);
        ELSE
          MkDynamicChildNames(kid, pMod);
        END;
      END;
    END MkStaticChildNames;
   (* ---------------------------------------------- *)
  BEGIN
    root^.clrName := root^.name;
    MkStaticChildNames(root);
  END MakeAllClrNames;

(*====================================================*)

  MODULE LabelControl;
    (*
     *  In this version labels are global to module
     *)

    IMPORT 
        LabelType, BuffS, BuffCrd, BuffEol, WriteObjByte;

    EXPORT 
        AllocLabel, TheLabel, EmitLabel;

    VAR top : LabelType;
        current : CARDINAL;

    PROCEDURE AllocLabel(VAR lab : LabelType);
    BEGIN
      INC(top);
      lab := top;
    END AllocLabel;

    PROCEDURE TheLabel(lab : LabelType);
    BEGIN
      BuffS("label");
      BuffCrd(lab);
    END TheLabel;

    PROCEDURE EmitLabel(lab : LabelType);
    BEGIN
      BuffS("label");
      BuffCrd(lab);
      WriteObjByte(':'); BuffEol;
    END EmitLabel;

  BEGIN
    top := 0;
    current := 1;
  END LabelControl;
  (*============================================================*)

  (*============================================================*)
  MODULE ProcState;
    IMPORT 
        PointerTo, TyNodeClass, CreateTypeDesc, invalid,
        IdDesc, IdString, IdNodeClass, IdTree, FormalClass,
        TypeDesc, CreateIdDesc, anonBkt, Object, thisCompileUnit,
        InitCursor, ElemPtr, LinkRight, GetNext, Ended, ClearPin,
        LookupInThisScope, FormalType, VarUses, Align, sPtrBkt,
        hasXSR, inXSR, lexLevel, Assert, TempIndex, TempList,
        ALLOCATE, DEALLOCATE, APPEND, CUT;

    EXPORT 
        InitCodeGen, ResetCodeGen, localHigh, localElem, 
        parOrdinal, notPar, current, DefineXSR, 
        newTemp, newPinTemp, newObjTemp, 
        FreeTemp, NewGroup, FreeGroup;

   (* --------------------------------------------------- *)

    CONST notPar  = 0FFFFH;
    TYPE  TypeMap = ARRAY [0 .. 3] OF TypeDesc;
    
    VAR localList : IdString;
        lValid    : BOOLEAN;
        lNext     : INTEGER;

        typeMap   : TypeMap;
        theProc   : IdDesc;

   (* --------------------------------------------------- *)

    PROCEDURE getTemp(typ : TypeDesc) : CARDINAL;
      VAR newId : IdDesc;
          index : INTEGER;
     (* ----------------------------------------------- *)
      PROCEDURE sameType(l,r : TypeDesc) : BOOLEAN;
      BEGIN
        IF l = r THEN RETURN TRUE;
        ELSIF (l^.tyClass = pointers) AND (r^.tyClass = pointers) OR
              (l^.tyClass = managedRef) AND (r^.tyClass = managedRef) THEN
          RETURN sameType(l^.targetType, r^.targetType);
        ELSE 
          RETURN FALSE;
        END;
      END sameType;
     (* ----------------------------------------------- *)
    BEGIN
      FOR index := 0 TO HIGH(localList) DO
        WITH localList[index]^ DO
          IF sameType(varType, typ) AND (normalRef = TRUE) THEN 
            normalRef := FALSE;
            RETURN index+1;
          END;
        END;
      END;
    (* Else must create new descriptor *)
      CreateIdDesc(anonBkt, newId, varNode);
      WITH newId^ DO
        varOffset := lNext; INC(lNext);
        varType   := typ;
        normalRef := FALSE;
      END;
      APPEND(localList, newId);
      RETURN lNext; (* Note: local ordinal is varOffset-1 *)
    END getTemp;    (* varOffset = 0 ==> not allocated!   *)

   (* --------------------------------------------------- *)

    PROCEDURE newObjTemp(obj : Object) : CARDINAL;
      VAR typ : TypeDesc;
    BEGIN
      CASE obj OF
      | byteInt, byteCard  : 
                    typ := typeMap[0];
      | shortInt,  shortCard : 
                    typ := typeMap[1];
      | longInt, longCard, word : 
                    typ := typeMap[2];
      | hugeInt   : typ := typeMap[3];
      | float     : typ := PointerTo(floats);
      | double    : typ := PointerTo(doubles);
      END;
      RETURN getTemp(typ);
    END newObjTemp;

   (* --------------------------------------------------- *)

    PROCEDURE newTemp(typ : TypeDesc) : CARDINAL;
    BEGIN
      IF typ^.tyClass = enums THEN RETURN getTemp(typeMap[0]);
      ELSIF typ^.tyClass = subranges THEN 
        CASE typ^.size OF
        | 1 : RETURN getTemp(typeMap[0]);
        | 2 : RETURN getTemp(typeMap[1]);
        | 4 : RETURN getTemp(typeMap[2]);
        | 8 : RETURN getTemp(typeMap[3]);
        END;
      ELSE
        RETURN getTemp(typ);
      END;
    END newTemp;

   (* --------------------------------------------------- *)

    PROCEDURE newPinTemp(typ : TypeDesc) : CARDINAL;
      VAR ref : TypeDesc;
    BEGIN
      CreateTypeDesc(thisCompileUnit, ref, pointers);
      ref^.targetType := typ;
      ref^.tyClass := managedRef;
      RETURN getTemp(ref);
    END newPinTemp;

   (* --------------------------------------------------- *)

    PROCEDURE FreeTemp(ord : CARDINAL);
    BEGIN
      IF ord # invalid THEN 
        WITH localList[ord-1]^ DO
          IF varType^.tyClass = managedRef THEN ClearPin(ord) END;
          normalRef := TRUE;
        END;
      END;
    END FreeTemp;

   (* --------------------------------------------------- *)

    PROCEDURE NewGroup(VAR grp : TempList);
    BEGIN
      NEW(grp,4);
    END NewGroup;

   (* --------------------------------------------------- *)

    PROCEDURE FreeGroup(grp : TempList);
      VAR tmp : TempIndex;
          idx : INTEGER;
    BEGIN
      IF grp # NIL THEN
        FOR idx := 0 TO HIGH(grp) DO FreeTemp(grp[idx]) END;
        DISPOSE(grp);
      END;
    END FreeGroup;

   (* --------------------------------------------------- *)

    PROCEDURE localHigh() : INTEGER;
    BEGIN
      Assert(lValid);
      RETURN HIGH(localList);
    END localHigh;

   (* --------------------------------------------------- *)

    PROCEDURE localElem(indx : INTEGER) : IdDesc;
    BEGIN
      Assert(lValid);
      RETURN localList[indx];
    END localElem;

   (* --------------------------------------------------- *)

    PROCEDURE current() : IdDesc;
    BEGIN
      RETURN theProc;
    END current;

   (* --------------------------------------------------- *)

    PROCEDURE InitCodeGen(proc : IdDesc);
      VAR rec : IdDesc; (* the XSR instance *)
    BEGIN
     (* QUESTION: does this get dynamic module data? *)
      lNext  := 0;
      lValid := TRUE;
      IF hasXSR(proc) THEN  (* XSR is always local-0 *)
        CreateIdDesc(anonBkt, rec, varNode);
        rec^.varType := proc^.exStRc;
        rec^.varOffset := 0; INC(lNext);
        APPEND(localList, rec);
      END;
      ListTree(proc^.scope);
      theProc := proc;
    END InitCodeGen;

   (* --------------------------------------------------- *)

    PROCEDURE ResetCodeGen();
    BEGIN
      lValid := FALSE;
      CUT(localList, -1);
    END ResetCodeGen;

   (* --------------------------------- *)

    PROCEDURE ListTree(tree : IdTree);
    BEGIN
     (*
      *  If needed, the XSR has already been defined.
      *  Here we must be careful not to clobber the
      *  local-var offsets assigned by DefineXSR.
      *)
      IF tree <> NIL THEN
        WITH tree^.ident^ DO
          IF (idClass = varNode) AND 
             (varClass = auto)   AND
              NOT (uplevAcc IN varUseSet) THEN 
            varOffset := lNext; INC(lNext);
            APPEND(localList, tree^.ident);
          END;
        END;
        ListTree(tree^.left); ListTree(tree^.right);
      END;
    END ListTree;
    
   (* ------------------------------------------------------ * 
    * ------------------------------------------------------ *)
    PROCEDURE parOrdinal(id : IdDesc) : INTEGER;
    BEGIN
      IF inXSR(id) AND (id^.hiDepth # notPar) THEN
        RETURN id^.hiDepth;
      ELSE
        RETURN id^.varOffset;
      END;
    END parOrdinal;

   (* ------------------------------------------------------ * 
    *  Define an eXplicit Stack-allocated activation Record  *
    *  for all data that is accessed from nested procedures. *
    *  The type descriptor is stored in the exStRc field.    *
    * ------------------------------------------------------ *)
    PROCEDURE DefineXSR(ths : IdDesc);
      VAR idx : INTEGER;  (* iteration count    *)
          off : INTEGER;  (* current XSR offset *)
          ord : CARDINAL; (* parameter ordinal  *)
          typ : TypeDesc;
          fld : IdDesc;
          crs : ElemPtr;
          prm : FormalType;
          frm : FormalClass;
     (* ----------------------------------------------- *)
      PROCEDURE LinkXsrField(tp : TypeDesc;
                             id : IdDesc;
                             nm : CARDINAL;
                         VAR os : INTEGER);
      BEGIN
        os := Align(os, id^.varType^.alignMask);
        LinkRight(tp^.fieldSeq, id);
        id^.varOffset := os;  (* field offset in XSR  *)
        id^.hiDepth   := nm;  (* param ordinal in CLR *)
       (*
        *  Update the offset of the client descriptor
        *)
        IF id^.idClass = fieldNode THEN 
          id^.enclFrm^.varOffset := os;
          id^.enclFrm^.hiDepth   := nm;
        END;
        INC(os, id^.varType^.size);
      END LinkXsrField;
     (* ----------------------------------------------- *)
      PROCEDURE proxyOf(frm : FormalType; fld : IdDesc) : IdDesc;
        VAR prx : IdDesc;
            typ : TypeDesc;
      BEGIN
        CreateIdDesc(frm^.fNam, prx, fieldNode);
       (*
        *  This proxy may have a different type to the
        *  formal arg from which it was copied.  Nevertheless
        *  the varOffset field of the varNode must match.
        *)
        prx^.enclFrm := fld;
        CASE frm^.form OF
        | varForm, openValForm, openVarForm :
            CreateTypeDesc(thisCompileUnit, typ, pointers);
            typ^.targetType := frm^.type;
        ELSE
          typ := frm^.type;
        END;
        prx^.fieldType := typ;
        RETURN prx;
      END proxyOf;
     (* ----------------------------------------------- *)
      PROCEDURE TreeRecurse(tr : IdTree; 
                            ty : TypeDesc; 
                        VAR os : INTEGER);
        VAR fd : IdDesc;
      BEGIN
        IF tr <> NIL THEN
          fd := tr^.ident;
          WITH fd^ DO
            IF (idClass = varNode) AND 
               (varClass = auto)   AND
               (uplevAcc IN varUseSet) THEN LinkXsrField(ty, fd, notPar, os);
            END;
          END;
          TreeRecurse(tr^.left, ty, os); TreeRecurse(tr^.right, ty, os);
        END;
      END TreeRecurse;
     (* ----------------------------------------------- *)
    BEGIN
      Assert(hasXSR(ths));
     (*
      *  Define the offsets of the uplevel accessed 
      *  data in the XSR, for both args and locals.
      *)
      off := 0;
      ord := 0;
      CreateTypeDesc(thisCompileUnit, typ, records);
      CreateIdDesc(sPtrBkt, fld, varNode);
      fld^.varType := PointerTo(adrs);
      LinkRight(typ^.fieldSeq, fld);
      fld^.fieldOffset := off; INC(off, 4);
      ths^.exStRc := typ;
     (*
      *  Now the args ...
      *)
      IF lexLevel(ths) > 1 THEN INC(ord) END; (* allow for static link *)
      InitCursor(ths^.procType^.params, crs);
      WHILE NOT Ended(crs) DO
        GetNext(crs, prm); 
        frm := prm^.form;
        LookupInThisScope(ths^.scope, prm^.fNam, fld);
        IF inXSR(fld) THEN LinkXsrField(typ, proxyOf(prm, fld), ord, off) END;
        INC(ord);

        IF (frm = openValForm) OR (frm = openVarForm) THEN 
          WHILE fld^.nextHigh # NIL DO
            fld := fld^.nextHigh; 
            IF inXSR(fld) THEN LinkXsrField(typ, fld, ord, off) END;
            INC(ord);
          END;
        END;
      END;
     (*
      *  Now the locals ...
      *)
      TreeRecurse(ths^.scope, typ, off);
    END DefineXSR;

   (* ------------------------------------------------- *)

  BEGIN
    NEW(localList, 8);
    ResetCodeGen;
    CreateTypeDesc(NIL, typeMap[0], subranges); 
    CreateTypeDesc(NIL, typeMap[1], subranges); 
    CreateTypeDesc(NIL, typeMap[2], subranges); 
    CreateTypeDesc(NIL, typeMap[3], subranges); 
    typeMap[0]^.size := 1;
    typeMap[1]^.size := 2;
    typeMap[2]^.size := 4;
    typeMap[3]^.size := 8;
  END ProcState;
  (*============================================================*)

  (*============================================================*)
  MODULE BlobTypes;
    IMPORT 
        newTemp, TypeDesc, TyNodeClass, 
        workList, thisCompileUnit, CreateTypeDesc;

    EXPORT 
        newBlobTypeTemp;

    (* 
     *  Find an array type which is equivalent in the CLR rep.
     *  This means an array with the same size (or greater).
     *)
    PROCEDURE equivType(size : CARDINAL) : TypeDesc;
      VAR type : TypeDesc;
          indx : INTEGER;
    BEGIN
      indx := 0;
      type := NIL;
      WHILE indx <= HIGH(workList) DO
        type := workList[indx];
        IF (type^.tyClass = arrays) AND 
           (type^.size >= size) AND
           (type^.size <= size * 3 DIV 2)  THEN RETURN type;
        ELSE INC(indx);
        END;
      END;
      CreateTypeDesc(thisCompileUnit, type, arrays); 
      type^.size := size;
      RETURN type;
    END equivType;

    PROCEDURE newBlobTypeTemp(size : CARDINAL) : CARDINAL;
    BEGIN
      RETURN newTemp(equivType(size));
    END newBlobTypeTemp;

  END BlobTypes;
  (*============================================================*)

  (*============================================================*)

    PROCEDURE Duplicate;
    BEGIN
      BuffI(opc_dup); BuffEol;
    END Duplicate;

    PROCEDURE Pop;
    BEGIN
      BuffI(opc_pop); BuffEol;
    END Pop;

   (* --------------------------------- *)

    PROCEDURE LineNum(num : CARDINAL);
    BEGIN
      BuffS("  .line "); BuffCrd(num); BuffS(" '"); 
      BuffS(inpName); BuffS("'"); BuffEol;
    END LineNum;

    PROCEDURE CodeLabel(sno : LabelType);
    BEGIN
      EmitLabel(sno);
    END CodeLabel;

    PROCEDURE CommentLabel(sno : LabelType; str : ARRAY OF CHAR);
    BEGIN
      TheLabel(sno); BuffS(":	// "); BuffS(str); BuffEol;
    END CommentLabel;

    PROCEDURE Branch(lab : LabelType);
    BEGIN
      BuffI(opc_br);
      TheLabel(lab);
      BuffEol;
    END Branch;

    PROCEDURE BranchEQZ(lab : LabelType);
    BEGIN
      BuffI(opc_brfalse);
      TheLabel(lab);
      BuffEol;
    END BranchEQZ;

    PROCEDURE BranchNEZ(lab : LabelType);
    (* pre  : a word (possibly Boolean) is on top of the stack  *)
    (* post : branch taken if equal/not equal to zero. Pop(1)   *)
    BEGIN
      BuffI(opc_brtrue);
      TheLabel(lab);
      BuffEol;
    END BranchNEZ;

  (*============================================================*)
  (*============================================================*)

    PROCEDURE PushInt(val : INTEGER);
    BEGIN
      CASE val OF 
      | -1 : BuffI(opc_ldc_i4_M1);
      |  0 : BuffI(opc_ldc_i4_0);
      |  1 : BuffI(opc_ldc_i4_1);
      |  2 : BuffI(opc_ldc_i4_2);
      |  3 : BuffI(opc_ldc_i4_3);
      |  4 : BuffI(opc_ldc_i4_4);
      |  5 : BuffI(opc_ldc_i4_5);
      |  6 : BuffI(opc_ldc_i4_6);
      |  7 : BuffI(opc_ldc_i4_7);
      |  8 : BuffI(opc_ldc_i4_8);
      ELSE
        IF (val >= -128) AND (val <= 127) THEN
          BuffI(opc_ldc_i4_s); BuffInt(val);
        ELSE
          BuffI(opc_ldc_i4);   BuffInt(val);
        END;
      END;
      BuffEol;
    END PushInt;

  (* ============================================== *)

    PROCEDURE PushHugeMax();
    BEGIN                  (* --- 5432109876543210 --- *)
      BuffI(opc_ldc_i8); BuffS("0x7fffffffffffffff"); BuffEol;
    END PushHugeMax;

    PROCEDURE PushHugeMin();
    BEGIN                  (* --- 5432109876543210 --- *)
      BuffI(opc_ldc_i8); BuffS("0x8000000000000000"); BuffEol;
    END PushHugeMin;

    PROCEDURE PushHuge(val : HugeInts.HUGEINT);
    BEGIN
      BuffI(opc_ldc_i8); BuffHuge(val); BuffEol;
    END PushHuge;

  (* ============================================== *)

    PROCEDURE PushCrd(val : CARDINAL);
    BEGIN
      CASE val OF 
      | 0 : BuffI(opc_ldc_i4_0);
      | 1 : BuffI(opc_ldc_i4_1);
      | 2 : BuffI(opc_ldc_i4_2);
      | 3 : BuffI(opc_ldc_i4_3);
      | 4 : BuffI(opc_ldc_i4_4);
      | 5 : BuffI(opc_ldc_i4_5);
      | 6 : BuffI(opc_ldc_i4_6);
      | 7 : BuffI(opc_ldc_i4_7);
      | 8 : BuffI(opc_ldc_i4_8);
      ELSE
        IF val <= 127 THEN
          BuffI(opc_ldc_i4_s); BuffCrd(val);
        ELSE
          BuffI(opc_ldc_i4);   BuffCrd(val);
        END;
      END;
      BuffEol;
    END PushCrd;

  (* ============================================== *)

    PROCEDURE PushChr(val : CHAR);
    BEGIN
      PushCrd(ORD(val));
    END PushChr;

  (*============================================================*)
  (*============================================================*)

    PROCEDURE PushLocalVal(ord : INTEGER);
    BEGIN
      CASE ord OF
      | 0 : BuffI(opc_ldloc_0);
      | 1 : BuffI(opc_ldloc_1);
      | 2 : BuffI(opc_ldloc_2);
      | 3 : BuffI(opc_ldloc_3);
      ELSE
        IF ord < 255 THEN
          BuffI(opc_ldloc_s); BuffCrd(ord);
        ELSE
          BuffI(opc_ldloc); BuffCrd(ord);
        END;
      END;
    END PushLocalVal;

  (* ============================================== *)

    PROCEDURE PushLocIdVal(id : IdDesc);
    BEGIN
      IF inXSR(id) THEN
        PushLocalAdr(0); BuffEol;
        AddOffset(id^.varOffset);
        LoadIndByType(id^.varType); 
      ELSE
        PushLocalVal(id^.varOffset); BuffEol;
      END;
    END PushLocIdVal;

  (*============================================================*)

    PROCEDURE StoreLocalVal(ord : INTEGER);
    BEGIN
      CASE ord OF
      | 0 : BuffI(opc_stloc_0);
      | 1 : BuffI(opc_stloc_1);
      | 2 : BuffI(opc_stloc_2);
      | 3 : BuffI(opc_stloc_3);
      ELSE
        IF ord < 255 THEN
          BuffI(opc_stloc_s); BuffCrd(ord);
        ELSE
          BuffI(opc_stloc); BuffCrd(ord);
        END;
      END;
    END StoreLocalVal;

  (* ============================================== *)

    PROCEDURE StoreLocIdVal(id : IdDesc);
      VAR temp : CARDINAL;
    BEGIN
      IF inXSR(id) THEN
        WriteComment("store local uplevel value");
        temp := newTemp(id^.varType);
        StoreTemp(temp);
        PushLocalAdr(0); BuffEol;
        AddOffset(id^.varOffset);
        PushTemp(temp);
        StoreIndByType(id^.varType); 
        FreeTemp(temp);
      ELSE
        StoreLocalVal(id^.varOffset); BuffEol;
      END;
    END StoreLocIdVal;

  (*============================================================*)

    PROCEDURE PushArgVal(ord : INTEGER);
    BEGIN
      CASE ord OF
      | 0 : BuffI(opc_ldarg_0);
      | 1 : BuffI(opc_ldarg_1);
      | 2 : BuffI(opc_ldarg_2);
      | 3 : BuffI(opc_ldarg_3);
      ELSE
        IF ord < 255 THEN
          BuffI(opc_ldarg_s); BuffInt(ord);
        ELSE
          BuffI(opc_ldarg); BuffInt(ord);
        END;
      END;
    END PushArgVal;

  (* ============================================== *)

    PROCEDURE CopyArg(n : INTEGER);
    BEGIN
      PushArgVal(n); BuffEol;
    END CopyArg;

  (* ============================================== *)

    PROCEDURE PushArgIdVal(id : IdDesc);
    BEGIN
      IF inXSR(id) THEN
        WriteComment("push arg uplevel value");
        PushLocalAdr(0); BuffEol;
        AddOffset(id^.varOffset);
        LoadIndByType(id^.varType); 
      ELSE
        PushArgVal(id^.varOffset); BuffEol;
      END;
    END PushArgIdVal;

  (*============================================================*)

    PROCEDURE StoreArgVal(ord : INTEGER);
    BEGIN
      IF ord < 255 THEN
        BuffI(opc_starg_s); BuffInt(ord);
      ELSE
        BuffI(opc_starg); BuffInt(ord);
      END;
    END StoreArgVal;

  (* ============================================== *)

    PROCEDURE StoreArgIdVal(id : IdDesc);
    BEGIN
      IF inXSR(id) THEN
WriteComment("store arg uplevel value");
(* FIXME : Wrong stack order *)
BuffS("WRONG STACK ORDER?");
        BuffI(opc_ldloc_0);  BuffEol;
        AddOffset(id^.varOffset);
        StoreIndByType(id^.varType); 
      ELSE
        StoreArgVal(id^.varOffset); BuffEol;
      END;
    END StoreArgIdVal;

  (*============================================================*)

  (*============================================================*)

  (*==================================*)
  (*   Anonymous temporary handling   *)
  (*==================================*)

    PROCEDURE PushTemp(tmp : CARDINAL);
    BEGIN
      PushLocalVal(tmp-1);
      BuffEol;
    END PushTemp;

    PROCEDURE PushTempAdr(tmp : CARDINAL);
    BEGIN
      PushLocalAdr(tmp-1);
      BuffEol;
    END PushTempAdr;

    PROCEDURE MakeTemp(tmp : CARDINAL);
    BEGIN
      BuffI(opc_dup); BuffEol;
      StoreLocalVal(tmp-1); BuffEol;
    END MakeTemp;

    PROCEDURE StoreTemp(tmp : CARDINAL);
    BEGIN
      StoreLocalVal(tmp-1); BuffEol;
    END StoreTemp;

    PROCEDURE ClearPin(tmp : CARDINAL);
    BEGIN
      WriteComment("clearing pin");
      BuffI(opc_ldnull);    BuffEol;
      StoreLocalVal(tmp-1); BuffEol;
    END ClearPin;

  (*===================================================*)

    PROCEDURE PreDecAndPushTemp(tmp : TempIndex);
    BEGIN
      PushLocalVal(tmp-1);  BuffEol;
      BuffI(opc_ldc_i4_1);  BuffEol;
      BuffI(opc_sub);       BuffEol;
      BuffI(opc_dup);       BuffEol;
      StoreLocalVal(tmp-1); BuffEol;
    END PreDecAndPushTemp;

    PROCEDURE PushAndPostIncTemp(tmp : TempIndex; inc : INTEGER);
    BEGIN
      PushLocalVal(tmp-1);          BuffEol;
      BuffI(opc_dup);               BuffEol;
      PushInt(inc); BuffI(opc_add);
      StoreLocalVal(tmp-1);         BuffEol;
    END PushAndPostIncTemp;

  (*===================================================*)

    PROCEDURE PushLocalAdr(ord : INTEGER);
    BEGIN
      IF ord < 255 THEN
        BuffI(opc_ldloca_s); BuffInt(ord);
      ELSE
        BuffI(opc_ldloca); BuffInt(ord);
      END;
    END PushLocalAdr;

  (* ============================================== *)

    PROCEDURE PushLocIdAdr(id : IdDesc);
    BEGIN
      IF inXSR(id) THEN
        WriteComment("push local uplevel adr");
        PushLocalAdr(0); BuffEol;
        AddOffset(id^.varOffset);
      ELSE
        PushLocalAdr(id^.varOffset); BuffEol;
      END;
    END PushLocIdAdr;

  (* ============================================== *)

    PROCEDURE PushLocPtrVal(id : IdDesc);
    BEGIN
      IF inXSR(id) THEN
        PushLocalAdr(0); BuffEol;
        AddOffset(id^.varOffset);
        LoadInd(word); 
      ELSE
        PushLocalVal(id^.varOffset); BuffEol;
      END;
    END PushLocPtrVal;

  (* ============================================== *)

    PROCEDURE PushArgPtrVal(id : IdDesc);
    BEGIN
      IF inXSR(id) THEN
        PushLocalAdr(0); BuffEol;
        AddOffset(id^.varOffset);
        LoadInd(word); 
      ELSE
        PushArgVal(id^.varOffset); BuffEol;
      END;
    END PushArgPtrVal;

  (*===================================================*)

    PROCEDURE PushArgAdr(ord : INTEGER);
    BEGIN
      IF ord < 255 THEN
          BuffI(opc_ldarga_s); BuffInt(ord);
      ELSE
          BuffI(opc_ldarga); BuffInt(ord);
      END;
    END PushArgAdr;

  (* ============================================== *)

    PROCEDURE PushArgIdAdr(id : IdDesc);
    BEGIN
      IF inXSR(id) THEN
        WriteComment("push arg uplevel adr");
        PushLocalAdr(0); BuffEol;
        AddOffset(id^.varOffset);
      ELSE
        PushArgAdr(id^.varOffset); BuffEol;
      END;
    END PushArgIdAdr;

  (*===================================================*)

    PROCEDURE CallMth(id : IdDesc; nPar,nRet : CARDINAL);
    (* nPar, nRet are needed for stack tracking *)
    BEGIN
      BuffIx(opc_call, (INT(nRet) - INT(nPar)));
      EmitResTypeName(id^.procType^.result); Space;
      BuffH(clrRefName(id)); 
      EmitCallSig(id); BuffEol;
    END CallMth;

    PROCEDURE CallTos(ty : TypeDesc; nPar,nRet : CARDINAL; link : BOOLEAN);
    (* nPar, nRet are needed for stack tracking *)
    BEGIN
      BuffIx(opc_calli, (INT(nRet) - INT(nPar)));
      EmitResTypeName(ty^.result); Space;
      EmitParSig(ty, link, FALSE); BuffEol;
    END CallTos;

  (*===================================================*)

    PROCEDURE MkTrap(trp : TrapEnum);
      CONST 
        mkstr  = "instance void [mscorlib]System.Exception::'.ctor'(string)";
        extTrp = "void [mscorlib]System.Environment::Exit(int32)";
        timTrp = "int32 [M2ClrRts]Traps::timeTrap()";
        mangle = "string [M2ClrRts]Traps::mangle";
        mnglI1 = "(int32,string)";
        sAdjI1 = -1;
        mnglI2 = "(int32,int32,string)";
        sAdjI2 = -2;
        mnglI3 = "(int32,int32,int32,string)";
        sAdjI3 = -3;
        mnglU1 = "(unsigned int32,string)";
        mnglU2 = "(unsigned int32,unsigned int32,string)";
        mnglU3 = "(unsigned int32,unsigned int32,unsigned int32,string)";
        mnglSS = "(unsigned int8*, unsigned int32)";
    BEGIN
     (* construct a exception object with a message *)
     (* then throw the new exception                *)
      IF trp = exitTrp THEN
        BuffIx(opc_call, sAdjI1); BuffS(extTrp); BuffEol;
      ELSIF trp = timeTrp THEN
        BuffIx(opc_call, 1); BuffS(timTrp); BuffEol;
      ELSIF trp = assTrp THEN
        BuffIx(opc_call, sAdjI1); BuffS(mangle); BuffEol;
        HTab; HTab; BuffS(mnglSS); BuffEol;
        BuffIx(opc_newobj, 0); BuffS(mkstr); BuffEol;
        BuffI(opc_throw); BuffEol;
      ELSE
        BuffI(opc_ldstr);
        CASE trp OF
        | minIntTrp: QuStr("Attempted negation of MIN(INTEGER)"); BuffEol; 
        | abortTrp : QuStr("Program executed ABORT");        BuffEol; 
        | modTrp   : QuStr("DIV or MOD on negative value");  BuffEol; 
        | funTrp   : QuStr("Missing function return value"); BuffEol; 
        | casTrpI  : QuStr("CASE trap: ordinal %");
                     BuffEol; 
                     BuffIx(opc_call, sAdjI1); BuffS(mangle); BuffEol; 
                     HTab; HTab; BuffS(mnglI1);              BuffEol;
        | casTrpU  : QuStr("CASE trap: ordinal %");
                     BuffEol; 
                     BuffIx(opc_call, sAdjI1); BuffS(mangle); BuffEol; 
                     HTab; HTab; BuffS(mnglU1);              BuffEol;
        | indexLHI : QuStr("Index bounds error: % not in [% .. %]");
                     BuffEol; 
                     BuffIx(opc_call, sAdjI3); BuffS(mangle); BuffEol; 
                     HTab; HTab; BuffS(mnglI3);              BuffEol;
        | indexLHU : QuStr("Index bounds error: % not in [% .. %]");
                     BuffEol; 
                     BuffIx(opc_call, sAdjI3); BuffS(mangle); BuffEol; 
                     HTab; HTab; BuffS(mnglU3);              BuffEol;
        | indexLI  : QuStr("Index bounds error: % less than %");
                     BuffEol; 
                     BuffIx(opc_call, sAdjI2); BuffS(mangle); BuffEol; 
                     HTab; HTab; BuffS(mnglI2);              BuffEol;
        | indexLU  : QuStr("Index bounds error: % less than %");
                     BuffEol; 
                     BuffIx(opc_call, sAdjI2); BuffS(mangle); BuffEol; 
                     HTab; HTab; BuffS(mnglU2);              BuffEol;
        | indexHI  : QuStr("Index bounds error: % greater than %");
                     BuffEol; 
                     BuffIx(opc_call, sAdjI2); BuffS(mangle); BuffEol; 
                     HTab; HTab; BuffS(mnglI2);              BuffEol;
        | indexHU  : QuStr("Index bounds error: % greater than %");
                     BuffEol; 
                     BuffIx(opc_call, sAdjI2); BuffS(mangle); BuffEol; 
                     HTab; HTab; BuffS(mnglU2);              BuffEol;
        | rangeLHI : QuStr("Range error: % not in [% .. %]");
                     BuffEol; 
                     BuffIx(opc_call, sAdjI3); BuffS(mangle); BuffEol; 
                     HTab; HTab; BuffS(mnglI3);              BuffEol;
        | rangeLHU : QuStr("Range error: % not in [% .. %]");
                     BuffEol; 
                     BuffIx(opc_call, sAdjI3); BuffS(mangle); BuffEol; 
                     HTab; HTab; BuffS(mnglU3);              BuffEol;
        | rangeLI  : QuStr("Range error: % less than %");
                     BuffEol; 
                     BuffIx(opc_call, sAdjI2); BuffS(mangle); BuffEol; 
                     HTab; HTab; BuffS(mnglI2);              BuffEol;
        | rangeLU  : QuStr("Range error: % less than %");
                     BuffEol; 
                     BuffIx(opc_call, sAdjI2); BuffS(mangle); BuffEol; 
                     HTab; HTab; BuffS(mnglU2);              BuffEol;
        | rangeHI  : QuStr("Range error: % greater than %");
                     BuffEol; 
                     BuffIx(opc_call, sAdjI2); BuffS(mangle); BuffEol; 
                     HTab; HTab; BuffS(mnglI2);              BuffEol;
        | rangeHU  : QuStr("Range error: % greater than %");
                     BuffEol; 
                     BuffIx(opc_call, sAdjI2); BuffS(mangle); BuffEol; 
                     HTab; HTab; BuffS(mnglU2);              BuffEol;
        END;
        BuffIx(opc_newobj, 0); BuffS(mkstr); BuffEol;
        BuffI(opc_throw); BuffEol;
      END;
    END MkTrap;

  (*===================================================*)

    PROCEDURE RtsHelper(enum : RtsCallEnum);
      CONST 
        voidSig = "void [M2ClrRts]Helper::";
        intSig  = "unsigned int32  [M2ClrRts]Helper::";
        args1   = "(int32*,unsigned int32)";
        args3   = "(int32*,int32*,int32*,unsigned int32)";
        lenArgs = "(unsigned int8*,unsigned int32)";
        rngArgs = "(int32*,unsigned int32,unsigned int32)";
    BEGIN
      IF enum = setRngIncl THEN 
        BuffIx(opc_call, -3); BuffS(voidSig); BuffS("rng"); BuffS(rngArgs);
      ELSIF enum = strLen  THEN 
        BuffIx(opc_call, -1); BuffS(intSig); BuffS("strLen"); BuffS(lenArgs);
      ELSE
        CASE enum OF
        | clr  : 
            BuffIx(opc_call, -2); BuffS(voidSig); BuffS("'clr'"); BuffS(args1);
        | cap3 : 
            BuffIx(opc_call, -4); BuffS(voidSig); BuffS("'cap'"); BuffS(args3);
        | cup3 : 
            BuffIx(opc_call, -4); BuffS(voidSig); BuffS("'cup'"); BuffS(args3);
        | xor3 : 
            BuffIx(opc_call, -4); BuffS(voidSig); BuffS("'xor'"); BuffS(args3);
        | dif3 : 
            BuffIx(opc_call, -4); BuffS(voidSig); BuffS("'dif'"); BuffS(args3);
        END;
      END;
      BuffEol;
    END RtsHelper;

  (*===================================================*)

    PROCEDURE CopyBlock(alignMask : CHAR);
    BEGIN
      BuffI(opc_cpblk); 
      BuffEol;
    END CopyBlock;

  (*===================================================*)

    PROCEDURE StoreVal(idnt : IdDesc;
                       mode : AccessMode;
                       objt : Object);

      TYPE  FSet    = SET OF FormalClass;
      CONST statics = FSet{static, export, extern};
      VAR   disp    : INTEGER;
            temp    : CARDINAL;
    BEGIN
      CASE mode OF
      | unresolved :  Assert(FALSE); 	(* assert: is a procedure address *)
      | directNonL :  (* a static field address *)
          BuffI(opc_stsfld); 
          EmitTypeSig(idnt^.varType); Space;
          BuffH(clrRefName(idnt));
          BuffEol; 
      | directLocl :
          IF idnt^.varClass IN statics THEN
            BuffI(opc_stsfld); 
            EmitTypeSig(idnt^.varType); Space;
            BuffH(clrRefName(idnt));
            BuffEol; 
          ELSIF idnt^.varClass = auto THEN (* local variable *)
            StoreLocIdVal(idnt);
          ELSE 
            StoreArgIdVal(idnt);
          END; 
      | highAccess :
          StoreArgIdVal(idnt);
      | indirect   : (* all VAR pars, with relative accesses *)
          temp := newObjTemp(objt); 
          StoreLocalVal(temp);
          IF idnt^.varClass = auto THEN (* local variable *)
            PushLocPtrVal(idnt);
          ELSE
            PushArgPtrVal(idnt);
          END;
          PushTemp(temp);
          StoreInd(objt);
          FreeTemp(temp);
      | uplevel, uplevelIndirect :
          temp := newObjTemp(objt); 
          StoreLocalVal(temp);
          PushDataLink(idnt);
          AddOffset(idnt^.varOffset);
          (*
           *  Adr of stack frame is now on top of stack
           *
           *  In the case of uplevel value arrays the
           *  offset is not known, so the array must be
           *  accessed indirectly via the parameter
           *)
          IF mode = uplevelIndirect THEN LoadInd(word) END;
          PushTemp(temp);
          StoreInd(objt);
          FreeTemp(temp);
      END; (* case *)
    END StoreVal;

  (*===================================================*)

    PROCEDURE PushAdr(idnt : IdDesc;
                      mode : AccessMode);
      TYPE  FSet    = SET OF FormalClass;
      CONST statics = FSet{static, export, extern};
      VAR   disp    : INTEGER;
    BEGIN
      CASE mode OF
      | unresolved :  (* assert: is a procedure variable name *)
          BuffI(opc_ldftn);
          EmitResTypeName(idnt^.procType^.result); Space;
          BuffH(clrRefName(idnt)); 
          EmitCallSig(idnt); BuffEol;
      | directNonL :  (* a static field address *)
          BuffI(opc_ldsflda); 
          EmitTypeSig(idnt^.varType); Space;
          BuffH(clrRefName(idnt));
          BuffEol; 
      | directLocl :
          IF idnt^.varClass IN statics THEN
            BuffI(opc_ldsflda); 
            EmitTypeSig(idnt^.varType); Space;
            BuffH(clrRefName(idnt));
            BuffEol; 
          ELSIF idnt^.varClass = auto THEN (* local variable *)
            PushLocIdAdr(idnt);
          ELSE 
            PushArgIdAdr(idnt);
          END; 
      | highAccess :
          PushArgIdAdr(idnt);
      | indirect   : (* all VAR pars, with relative accesses *)
          IF idnt^.varClass = auto THEN (* local variable *)
            PushLocPtrVal(idnt);
          ELSE
            PushArgPtrVal(idnt);
          END;
      | uplevel, uplevelIndirect :
          PushDataLink(idnt);
          AddOffset(idnt^.varOffset);
         (*
          *  Adr of datum is now on top of stack
          *
          *  In the case of uplevel value arrays the
          *  offset is not known, so the array must be
          *  accessed indirectly via the parameter
          *)
          IF mode = uplevelIndirect THEN LoadInd(word) END;
      END; (* case *)
    END PushAdr;

  (*===================================================*)

    PROCEDURE PushVal(idnt : IdDesc;
                      mode : AccessMode;
                      objt : Object);

      TYPE  FSet    = SET OF FormalClass;
      CONST statics = FSet{static, export, extern};
      VAR   disp    : INTEGER;
    BEGIN
      CASE mode OF
      | unresolved :  (* assert: is procedure value *)
          BuffI(opc_ldftn);
          EmitResTypeName(idnt^.procType^.result); Space;
          BuffH(clrRefName(idnt)); 
          EmitCallSig(idnt); BuffEol;
      | directNonL :  (* a static field address *)
          BuffI(opc_ldsfld); 
          EmitTypeSig(idnt^.varType); Space;
          BuffH(clrRefName(idnt));
          BuffEol; 
      | directLocl :
          IF idnt^.varClass IN statics THEN
            BuffI(opc_ldsfld); 
            EmitTypeSig(idnt^.varType); Space;
            BuffH(clrRefName(idnt));
            BuffEol; 
          ELSIF idnt^.varClass = auto THEN (* local variable *)
            PushLocIdVal(idnt);
          ELSE 
            PushArgIdVal(idnt);
          END; 
      | highAccess :
          PushArgIdVal(idnt);
      | indirect   : (* all VAR pars, with relative accesses *)
          IF idnt^.varClass = auto THEN (* local variable *)
            PushLocPtrVal(idnt);
          ELSE
            PushArgPtrVal(idnt);
          END;
          LoadInd(objt);   (* OR IS THIS LoadIndByType(idnt^.varType) ??? *)
      | uplevel, uplevelIndirect :
          PushDataLink(idnt);
          AddOffset(idnt^.varOffset);
         (*
          *  Adr of datum is now on top of stack
          *
          *  In the case of uplevel value arrays the
          *  offset is not known, so the array must be
          *  accessed indirectly via the parameter
          *)
          IF mode = uplevelIndirect THEN LoadInd(word) END;
          LoadInd(objt); 
      END; (* case *)
    END PushVal;

  (*===================================================*)

    PROCEDURE PushModName;
    BEGIN
      BuffI(opc_ldsfld); BuffS(" void* ");
      BuffS(thisName); Dot; BuffS(thisName); DColon; BuffN(modNamB); BuffEol;
    END PushModName;

  (*===================================================*)

    PROCEDURE PushCon(ofst : CARDINAL);
    BEGIN
      BuffI(opc_ldsfld); BuffS(" void* ");
      BuffS(thisName); Dot; BuffS(thisName); 
      DColon; BuffN(conDatB); BuffEol;
      IF ofst > 0 THEN 
        PushCrd(ofst); 
        BuffI(opc_add); BuffEol;
      END;
    END PushCon;

  (*============================================================*)
  (*============================================================*)

    TYPE ModeInst = ARRAY ModeEnum OF Instruction;

    PROCEDURE Add(mode : ModeEnum);
      CONST inst = ModeInst{opc_add, opc_add_ovf, opc_add_ovf_un};
    BEGIN
      BuffI(inst[mode]); BuffEol;
    END Add;

   (* ----------------------------------------------- *)

    PROCEDURE Sub(mode : ModeEnum);
      CONST inst = ModeInst{opc_sub, opc_sub_ovf, opc_sub_ovf_un};
    BEGIN
      BuffI(inst[mode]); BuffEol;
    END Sub;

   (* ----------------------------------------------- *)

    PROCEDURE Mul(mode : ModeEnum);
      CONST inst = ModeInst{opc_mul, opc_mul_ovf, opc_mul_ovf_un};
    BEGIN
      BuffI(inst[mode]); BuffEol;
    END Mul;

   (* ----------------------------------------------- *)

    PROCEDURE DivU();
    BEGIN
      BuffI(opc_div_un); BuffEol;
    END DivU;

    PROCEDURE DivI();
    BEGIN
      BuffIx(opc_call, -1); BuffS("int32 [M2ClrRts]Helper::divI(int32,int32)");
      BuffEol;
    END DivI;

    PROCEDURE DivH();
    BEGIN
      BuffIx(opc_call, -1); BuffS("int64 [M2ClrRts]Helper::divH(int64,int64)");
      BuffEol;
    END DivH;

   (* ----------------------------------------------- *)

    PROCEDURE ModU();
    BEGIN
      BuffI(opc_rem_un); BuffEol;
    END ModU;

    PROCEDURE ModI();
    BEGIN
      BuffIx(opc_call, -1); BuffS("int32 [M2ClrRts]Helper::modI(int32,int32)");
      BuffEol;
    END ModI;

    PROCEDURE ModH();
    BEGIN
      BuffIx(opc_call, -1); BuffS("int64 [M2ClrRts]Helper::modH(int64,int64)");
      BuffEol;
    END ModH;

   (* ----------------------------------------------- *)

    PROCEDURE RemU(); (* Same as ModU *)
    BEGIN
      BuffI(opc_rem_un); BuffEol;
    END RemU;

    PROCEDURE RemH();
    BEGIN
      BuffIx(opc_call, -1); BuffS("int64 [M2ClrRts]Helper::remH(int64,int64)");
      BuffEol;
    END RemH;

    PROCEDURE RemI();
    BEGIN
      BuffI(opc_rem); BuffEol;
    END RemI;

   (* ----------------------------------------------- *)

    PROCEDURE Slash(mode : ModeEnum);
      CONST inst = ModeInst{opc_div, opc_div, opc_div_un};
    BEGIN
      BuffI(inst[mode]); BuffEol;
    END Slash;

   (* ----------------------------------------------- *)

    PROCEDURE Neg();
    BEGIN
      BuffI(opc_neg); BuffEol;
    END Neg;

   (* ----------------------------------------------- *)

    PROCEDURE NegBits();
    BEGIN
      BuffI(opc_not); BuffEol;
    END NegBits;

   (* ----------------------------------------------- *)

    PROCEDURE NegBool();
    BEGIN
      BuffI(opc_ldc_i4_1); BuffEol;
      BuffI(opc_xor); BuffEol;
    END NegBool;

   (* ----------------------------------------------- *)

    PROCEDURE BitOR;
    BEGIN
      BuffI(opc_or); BuffEol;
    END BitOR;

   (* ----------------------------------------------- *)

    PROCEDURE BitAND;
    BEGIN
      BuffI(opc_and); BuffEol;
    END BitAND;

   (* ----------------------------------------------- *)

    PROCEDURE BitXOR;
    BEGIN
      BuffI(opc_xor); BuffEol;
    END BitXOR;

   (* ----------------------------------------------- *)

    PROCEDURE LShift;
    BEGIN
      BuffI(opc_shl); BuffEol;
    END LShift;

   (* ----------------------------------------------- *)

    PROCEDURE RShift;
    BEGIN
      BuffI(opc_shr); BuffEol;
    END RShift;

   (* ----------------------------------------------- *)

    PROCEDURE LRShift;
    BEGIN
      BuffI(opc_shr_un); BuffEol;
    END LRShift;

   (* ----------------------------------------------- *)

    PROCEDURE Shift;
      VAR tpLb, exLb : LabelType;
    BEGIN
      AllocLabel(tpLb);
      AllocLabel(exLb);
     (*
      *  This is a variable shift. Do it the hard way.
      *  First, check the sign of the right hand op.
      *)
      BuffI(opc_dup);                 BuffEol;
      BuffI(opc_ldc_i4_0);            BuffEol;
      BuffI(opc_blt); TheLabel(tpLb); BuffEol;
     (*
      *  Positive selector ==> shift left;
      *)
      BuffI(opc_shl);                 BuffEol;
      BuffI(opc_br); TheLabel(exLb);  BuffEol;
     (*
      *  Negative selector ==> shift right;
      *  Q: should this be an unsigned shift?
      *)
      CodeLabel(tpLb);
      BuffI(opc_neg);                 BuffEol;
      BuffI(opc_shr);                 BuffEol;
      CodeLabel(exLb);
    END Shift;

   (* ----------------------------------------------- *)

    PROCEDURE AddOffset(ofst : INTEGER);
    BEGIN
      IF ofst <> 0 THEN
        PushInt(ofst);
        BuffI(opc_add); 
        BuffEol;
      END;
    END AddOffset;

  (*============================================================*)
  (*============================================================*)

    PROCEDURE StoreInd(obj : Object);
      CONST storeTable = InstructionTable{
                   opc_stind_i1, opc_stind_i1, opc_stind_i2, 
                   opc_stind_i2, opc_stind_i4, opc_stind_i4, 
                   opc_stind_i4, opc_stind_i8, opc_stind_r4, opc_stind_r8};
    BEGIN
      BuffI(storeTable[obj]); BuffEol;
    END StoreInd;

  (*===================================================*)

    PROCEDURE StoreIndByType(typ : TypeDesc);
      VAR obj : Object;
    BEGIN
      WITH typ^ DO
        IF (tyClass IN TyClassSet{arrays,records}) OR
           (tyClass = sets) AND (typ^.size > bytesInWord) THEN
          StoreObj(typ);
        ELSIF tyClass = floats  THEN StoreInd(float);
        ELSIF tyClass = doubles THEN StoreInd(double);
        ELSIF tyClass = subranges THEN StoreIndByType(hostType);
        ELSE  CASE size OF
              | 1 : obj := byteInt;
              | 2 : obj := shortInt;
              | 4 : obj := longInt;
              | 8 : obj := hugeInt;
              END;
              StoreInd(obj);
        END;
      END;
    END StoreIndByType;

  (*===================================================*)

    PROCEDURE LoadInd(obj : Object);
      CONST loadTable = InstructionTable{
                   opc_ldind_i1, opc_ldind_u1, opc_ldind_i2, 
                   opc_ldind_u2, opc_ldind_i4, opc_ldind_u4, 
                   opc_ldind_i4, opc_ldind_i8, opc_ldind_r4, opc_ldind_r8};
    BEGIN
      BuffI(loadTable[obj]); BuffEol;
    END LoadInd;

  (*===================================================*)

    PROCEDURE LoadIndByType(typ : TypeDesc);
      VAR obj : Object;
    BEGIN
      WITH typ^ DO
        IF    tyClass = arrays  THEN
          IF typ^.indexType = PointerTo(cards) THEN 
            LoadInd(word);
          ELSE LoadObj(typ);
          END;
        ELSIF tyClass = records THEN LoadObj(typ);
        ELSIF tyClass = floats  THEN LoadInd(float);
        ELSIF tyClass = doubles THEN LoadInd(double);
        ELSIF tyClass = subranges THEN LoadIndByType(hostType);
        ELSIF IsSignedType(typ) THEN
              CASE size OF
              | 1 : obj := byteInt;
              | 2 : obj := shortInt;
              | 4 : obj := longInt;
              | 8 : obj := hugeInt;
              END;
              LoadInd(obj);
        ELSE  CASE size OF
              | 1 : obj := byteCard;
              | 2 : obj := shortCard;
              | 4 : obj := longCard;
              | 8 : obj := hugeInt;
              END;
              LoadInd(obj);
        END;
      END;
    END LoadIndByType;

  (*============================================================*)
  (*============================================================*)

    PROCEDURE LoadObj(dTyp : TypeDesc);
    BEGIN
      BuffI(opc_ldobj); EmitTypeSig(dTyp); BuffEol;
    END LoadObj;

  (*===================================================*)

    PROCEDURE StoreObj(dTyp : TypeDesc);
    BEGIN
      BuffI(opc_stobj); EmitTypeSig(dTyp); BuffEol;
    END StoreObj;

  (*============================================================*)
  (*============================================================*)

    PROCEDURE DFloat; 
    BEGIN
      BuffI(opc_conv_r8); BuffEol;
    END DFloat;

   (* ------------------------------------- *)

    PROCEDURE FFloat;
    BEGIN
      BuffI(opc_conv_r4); BuffEol;
    END FFloat;
 
   (* ------------------------------------- *)

    PROCEDURE DtoI(test : BOOLEAN);  (* NOT EXPORTED *)
    BEGIN
      IF test THEN
        BuffI(opc_conv_ovf_i4); 
      ELSE
        BuffI(opc_conv_i4); 
      END;
      BuffEol;
    END DtoI;

   (* ------------------------------------- *)

    PROCEDURE TruncU(test : BOOLEAN); 
    BEGIN 
      IF test THEN
        BuffI(opc_conv_ovf_u4); 
      ELSE
        BuffI(opc_conv_u4); 
      END;
      BuffEol;
    END TruncU;

   (* ------------------------------------- *)

    PROCEDURE TruncI(test : BOOLEAN); 
    BEGIN 
      IF test THEN
        BuffI(opc_conv_ovf_i4); 
      ELSE
        BuffI(opc_conv_i4); 
      END;
      BuffEol;
    END TruncI;

   (* ------------------------------------- *)

    PROCEDURE HTrunc(test : BOOLEAN);
    BEGIN
      IF test THEN
        BuffI(opc_conv_ovf_i8); 
      ELSE
        BuffI(opc_conv_i8); 
      END;
      BuffEol;
    END HTrunc;

    PROCEDURE HEntier(test : BOOLEAN);
    BEGIN
      BuffIx(opc_call, 0); 
      BuffS("float64 [mscorlib]System.Math::Floor(float64)"); BuffEol;
      HTrunc(test);
      BuffEol;
    END HEntier;

    PROCEDURE HRound(test : BOOLEAN);
    BEGIN
      BuffIx(opc_call, 0); 
      BuffS("float64 [mscorlib]System.Math::Round(float64)"); BuffEol;
      HTrunc(test);
      BuffEol;
    END HRound;

   (* ------------------------------------- *)

    PROCEDURE MkCrd; 
    BEGIN
      BuffI(opc_conv_r_un); BuffEol;
    END MkCrd;

    PROCEDURE MkR64; 
    BEGIN
      BuffI(opc_conv_r8); BuffEol;
    END MkR64;

    PROCEDURE MkR32;
    BEGIN
      BuffI(opc_conv_r4); BuffEol;
    END MkR32;

   (* ------------------------------------- *)

    PROCEDURE FloorD(test : BOOLEAN);
    BEGIN
      BuffIx(opc_call, 0); 
      BuffS("float64 [mscorlib]System.Math::Floor(float64)"); BuffEol;
      DtoI(test);
    END FloorD;

   (* ------------------------------------- *)

    PROCEDURE FloorF(test : BOOLEAN);
    BEGIN
      BuffI(opc_conv_r8); BuffEol;
      FloorD(test);
    END FloorF;

   (* ------------------------------------- *)

    PROCEDURE RoundD(test : BOOLEAN);
    BEGIN
      BuffIx(opc_call, 0);
      BuffS("float64 [mscorlib]System.Math::Round(float64)"); BuffEol;
      DtoI(test);
    END RoundD;

   (* ------------------------------------- *)

    PROCEDURE RoundF(test : BOOLEAN);
    BEGIN
      BuffI(opc_conv_r8); BuffEol;
      RoundD(test);
    END RoundF;

   (* ------------------------------------- *)

    PROCEDURE ConvItoI64();
    BEGIN
      BuffI(opc_conv_i8); BuffEol;
    END ConvItoI64;

    PROCEDURE ConvUtoI64();
    BEGIN
      BuffI(opc_conv_ovf_i8_un); BuffEol;
    END ConvUtoI64;

   (* ------------------------------------- *)

    PROCEDURE MkI32(test : BOOLEAN);
    BEGIN
      IF test THEN
        BuffI(opc_conv_ovf_i4); 
      ELSE
        BuffI(opc_conv_i4);
      END;
      BuffEol;
    END MkI32;

   (* ------------------------------------- *)

    PROCEDURE MkU32(test : BOOLEAN);
    BEGIN
      IF test THEN
        BuffI(opc_conv_ovf_u4); 
      ELSE
        BuffI(opc_conv_u4);
      END;
      BuffEol;
    END MkU32;

   (* ------------------------------------- *)

    PROCEDURE MkU8(test : BOOLEAN);
    BEGIN
      IF test THEN
        BuffI(opc_conv_ovf_u1);
      ELSE
        BuffI(opc_conv_u1);
      END;
      BuffEol;
    END MkU8;

  (*============================================================*)

    PROCEDURE PushZero(obj : Object);
    BEGIN
      IF    obj = float   THEN BuffI(opc_ldc_r4); BuffS("0.0");
      ELSIF obj = double  THEN BuffI(opc_ldc_r8); BuffS("0.0");
      ELSIF obj = hugeInt THEN BuffI(opc_ldc_i8); BuffS("0");
      ELSE                     BuffI(opc_ldc_i4_0);
      END;
      BuffEol;
    END PushZero;

  (*============================================================*)

    PROCEDURE AbsVal(obj : Object);
      VAR lab : LabelType;
    BEGIN
      AllocLabel(lab);
      BuffI(opc_dup); BuffEol;
      PushZero(obj);
      BuffI(opc_bge); TheLabel(lab); BuffEol;
      BuffI(opc_neg); BuffEol;
      CodeLabel(lab);
    END AbsVal;


  (*============================================================*)
  (*============================================================*)

    PROCEDURE SetInOp;
    BEGIN
      BuffI(opc_shr_un);   BuffEol;
      BuffI(opc_ldc_i4_1); BuffEol;
      BuffI(opc_and);      BuffEol;
    END SetInOp;

    PROCEDURE SetRelop (op : ExprNodeClass);  (* word sets *)
      VAR operator : Relops;
          temp     : CARDINAL;
    BEGIN
      operator := exprNodeToRelop[ORD(op) - eqOrd];
      CASE operator OF
        | geR : temp := newObjTemp(word);
                MakeTemp(temp);                  (* lOp, rOp ...          *)
                BuffI(opc_and); BuffEol;         (* lOpr*rOp ...          *)
                PushTemp(temp);                  (* lOp*rOp, rOp ...      *)
                BuffI(opc_ceq); BuffEol;         (* bool ...              *)
                FreeTemp(temp);
        | leR : temp := newObjTemp(word);
                MakeTemp(temp);                  (* lOp, rOp ...          *)
                BuffI(opc_or);  BuffEol;         (* lOpr+rOp ...          *)
                PushTemp(temp);                  (* lOp+rOp, rOp ...      *)
                BuffI(opc_ceq); BuffEol;         (* bool ...              *)
                FreeTemp(temp);
        | eqR : BuffI(opc_ceq); BuffEol;
        | neR : BuffI(opc_ceq); BuffEol; NegBool;
      END;
    END SetRelop;

    PROCEDURE BigSetRelop (op : ExprNodeClass);  (* word sets *)
     (* values on the stack are: (lOpAdr, rOpAdr, elNm) *)
      CONST 
        boolSig = "bool [M2ClrRts]Helper::";
        args2   = "(int32*,int32*,unsigned int32)";

      VAR operator : Relops;
    BEGIN
      operator := exprNodeToRelop[ORD(op) - eqOrd];
      BuffIx(opc_call, -2); BuffS(boolSig);
      CASE operator OF
        | geR : BuffS("setGE");
        | leR : BuffS("setLE");
        | eqR : BuffS("setEQ");
        | neR : BuffS("setNE");
      END;
      BuffS(args2); BuffEol;
    END BigSetRelop;

    PROCEDURE IntRelop (op : ExprNodeClass);
      VAR operator : Relops;
    BEGIN
      operator := exprNodeToRelop[ORD(op) - eqOrd];
      CASE operator OF
      | eqR : BuffI(opc_ceq); BuffEol;
      | neR : BuffI(opc_ceq); BuffEol; NegBool;
      | lsR : BuffI(opc_clt); BuffEol;
      | leR : BuffI(opc_cgt); BuffEol; NegBool;
      | gtR : BuffI(opc_cgt); BuffEol;
      | geR : BuffI(opc_clt); BuffEol; NegBool;
      END;
    END IntRelop;

    PROCEDURE FltRelop (op : ExprNodeClass);
      VAR operator : Relops;
    BEGIN
      operator := exprNodeToRelop[ORD(op) - eqOrd];
      CASE operator OF
      | eqR : BuffI(opc_ceq);    BuffEol;
      | neR : BuffI(opc_ceq);    BuffEol; NegBool;
      | lsR : BuffI(opc_clt);    BuffEol;
      | leR : BuffI(opc_cgt_un); BuffEol; NegBool;
      | gtR : BuffI(opc_cgt);    BuffEol;
      | geR : BuffI(opc_clt_un); BuffEol; NegBool;
      END;
    END FltRelop;

    PROCEDURE CardRelop (op : ExprNodeClass); 
      VAR operator : Relops;
    BEGIN
      operator := exprNodeToRelop[ORD(op) - eqOrd];
      CASE operator OF
      | eqR : BuffI(opc_ceq);    BuffEol;
      | neR : BuffI(opc_ceq);    BuffEol; NegBool;
      | gtR : BuffI(opc_cgt_un); BuffEol;
      | geR : BuffI(opc_clt_un); BuffEol; NegBool;
      | lsR : BuffI(opc_clt_un); BuffEol;
      | leR : BuffI(opc_cgt_un); BuffEol; NegBool;
      END;
    END CardRelop;

  (*============================================================*)

    PROCEDURE CardRelopTrue(op : ExprNodeClass; lab : LabelType);
      CONST table = RelopTable{
               opc_blt_un, opc_ble_un, opc_beq,
               opc_bgt_un, opc_bge_un, opc_bne_un};
      VAR operator : Relops;
    BEGIN
      operator := exprNodeToRelop[ORD(op) - eqOrd];
      BuffI(table[ORD(operator)]); TheLabel(lab);
      BuffEol;
    END CardRelopTrue;

    PROCEDURE CardRelopFalse(op : ExprNodeClass; lab : LabelType);
      CONST table = RelopTable{
               opc_bge_un, opc_bgt_un, opc_bne_un,
               opc_ble_un, opc_blt_un, opc_beq};
      VAR operator : Relops;
    BEGIN
      operator := exprNodeToRelop[ORD(op) - eqOrd];
      BuffI(table[ORD(operator)]); TheLabel(lab);
      BuffEol;
    END CardRelopFalse;

  (*============================================================*)

    PROCEDURE IntRelopTrue(op : ExprNodeClass; lab : LabelType);
      CONST table = RelopTable{
               opc_blt, opc_ble, opc_beq,
               opc_bgt, opc_bge, opc_bne_un};
      VAR operator : Relops;
    BEGIN
      operator := exprNodeToRelop[ORD(op) - eqOrd];
      BuffI(table[ORD(operator)]); TheLabel(lab);
      BuffEol;
    END IntRelopTrue;

    PROCEDURE IntRelopFalse(op : ExprNodeClass; lab : LabelType);
      CONST table = RelopTable{
               opc_bge, opc_bgt, opc_bne_un,
               opc_ble, opc_blt, opc_beq};
      VAR operator : Relops;
    BEGIN
      operator := exprNodeToRelop[ORD(op) - eqOrd];
      BuffI(table[ORD(operator)]); TheLabel(lab);
      BuffEol;
    END IntRelopFalse;

  (*============================================================*)

    PROCEDURE FltRelopTrue(op : ExprNodeClass; lab : LabelType);
      CONST table = RelopTable{
               opc_blt, opc_ble_un, opc_beq,
               opc_bgt, opc_bge_un, opc_bne_un};
      VAR operator : Relops;
    BEGIN
      operator := exprNodeToRelop[ORD(op) - eqOrd];
      BuffI(table[ORD(operator)]); TheLabel(lab);
      BuffEol;
    END FltRelopTrue;

    PROCEDURE FltRelopFalse(op : ExprNodeClass; lab : LabelType);
      CONST table = RelopTable{
               opc_bge_un, opc_bgt, opc_bne_un,
               opc_ble_un, opc_blt, opc_beq};
      VAR operator : Relops;
    BEGIN
      operator := exprNodeToRelop[ORD(op) - eqOrd];
      BuffI(table[ORD(operator)]); TheLabel(lab);
      BuffEol;
    END FltRelopFalse;

  (*============================================================*)
  (*============================================================*)

    PROCEDURE EmitFormal(id : FormalType);
      VAR indx : CARDINAL;
    BEGIN
      EmitFrmTypeSig(id^.type);
      CASE id^.form OF
      | valForm : Space; BuffN(id^.fNam);
      | varForm : Star; Space; BuffN(id^.fNam);
      | openValForm, openVarForm : 
          Star; HTab; BuffN(id^.fNam); Comma;
          FOR indx := 1 TO id^.dimN DO
            BuffEol; HTab; HTab; BuffH(crdHsh); HTab;
            BuffS("hi$"); BuffH(id^.fNam); BuffCrd(indx);
            IF indx < id^.dimN THEN Comma END;
          END;
      END;
    END EmitFormal;

    PROCEDURE EmitStaticLink;
      CONST linkSig = "void* 's$Lnk'";
    BEGIN
      BuffS(linkSig);
    END EmitStaticLink;

   (* ------------------------------------- *)

    PROCEDURE EmitFormalType(id : FormalType;
                             pi : BOOLEAN);
      VAR indx : CARDINAL;
    BEGIN
      EmitFrmTypeSig(id^.type);
      CASE id^.form OF
      | valForm : (* skip *)
      | varForm : Star;
      | openValForm, openVarForm : 
          Star;
          IF NOT pi THEN
            FOR indx := 1 TO id^.dimN DO
              Comma; BuffH(crdHsh); 
            END;
          END;
      END;
    END EmitFormalType;

   (* ------------------------------------- *)

    PROCEDURE EmitResTypeName(ty : TypeDesc);
    BEGIN
      IF ty = NIL THEN BuffS("void");
      ELSIF ty^.pubTag = opaqueAlias THEN 
        BuffH(voidStar); 
      ELSE 
        EmitTypeSig(ty);
      END;
    END EmitResTypeName;

   (* ------------------------------------- *)

    PROCEDURE EmitMethAttr(id : IdDesc);
    BEGIN
      WITH id^ DO
        IF idClass = procHeader THEN
          BuffS("public static ");
        ELSE
          BuffS("assembly static ");
        END;
        EmitResTypeName(id^.procType^.result);
      END;
    END EmitMethAttr;

   (* ------------------------------------- *)

    PROCEDURE EmitParSig(pTyp : TypeDesc; link,pInv : BOOLEAN);
      VAR curs : ElemPtr;
          parm : FormalType;
    BEGIN
      WriteObjByte("(");
      InitCursor(pTyp^.params, curs);
      IF link THEN 
        BuffEol; HTab; HTab;
        BuffH(voidStar);
        IF NOT Ended(curs) THEN Comma END;
      END;
      WHILE NOT Ended(curs) DO
        BuffEol; HTab; HTab;
        GetNext(curs, parm); 
        EmitFormalType(parm, pInv);
        IF NOT Ended(curs) THEN Comma END;
      END;
      WriteObjByte(")");
    END EmitParSig;

    PROCEDURE EmitCallSig(id : IdDesc);
      VAR pInv : BOOLEAN;
    BEGIN
      pInv := (id^.idClass = externProc) AND id^.module^.direct;
      EmitParSig(id^.procType, (lexLevel(id) > 1), pInv);
    END EmitCallSig;

   (* ------------------------------------- *)

    PROCEDURE EmitLocals(id : IdDesc);
      VAR indx : INTEGER;
          lLen : INTEGER;
          elem : IdDesc;
    BEGIN
      lLen := localHigh();
      BuffS("  .locals init ("); 
      FOR indx := 0 TO lLen DO
        elem := localElem(indx);
        BuffEol; HTab; EmitTypeSig(elem^.varType); 
        IF elem^.name = anonBkt THEN 
          IF indx < lLen THEN Comma END;
          HTab;
          BuffS("// anon temp");
        ELSE
          HTab;
          BuffN(elem^.name);
          IF indx < lLen THEN Comma END;
        END;
      END;
      BuffEol; HTab; WriteObjByte(")"); BuffEol;
    END EmitLocals;

  (* ================================================================= *)

    PROCEDURE EmitArgList(id : IdDesc);
     (* --------------------------------- *)
      PROCEDURE SetOrdinal(par : FormalType;
                           idx : CARDINAL;
                           scp : IdTree);
        VAR id : IdDesc;
      BEGIN
       (*
        *  If needed, the XSR has already been defined.
        *  Here we must be careful not to clobber the
        *  argument offsets assigned by DefineXSR.
        *)
        LookupInThisScope(scp, par^.fNam, id);
        IF NOT inXSR(id) THEN id^.varOffset := idx END;
        IF (par^.form = openValForm) OR
           (par^.form = openVarForm) THEN 
          WHILE id^.nextHigh # NIL DO
            id := id^.nextHigh; INC(idx);
            IF NOT inXSR(id) THEN id^.varOffset := idx END;
          END;
        END;
      END SetOrdinal;
     (* --------------------------------- *)
      VAR curs : ElemPtr;
          pTyp : TypeDesc;
          parm : FormalType;
          pLen : CARDINAL;
          lBrk : BOOLEAN;
          rStr : BOOLEAN;      (* ==> returns a strucure *)
          lLev : CARDINAL;
    BEGIN
      pTyp := id^.procType;
      lLev := lexLevel(id);

      WriteObjByte("(");
      pLen := 0;
      IF lLev > 1 THEN INC(pLen) END;
      InitCursor(pTyp^.params, curs);
      WHILE NOT Ended(curs) DO
        GetNext(curs, parm); 
        SetOrdinal(parm, pLen, id^.scope);
        INC(pLen);
        IF (parm^.form = openValForm) OR
           (parm^.form = openVarForm) THEN INC(pLen, parm^.dimN) END;
      END;

      lBrk := pLen >= 2;
      IF lLev > 1 THEN 
        EmitStaticLink;
        IF lBrk THEN Comma END;
      END;
      InitCursor(pTyp^.params, curs);
      WHILE NOT Ended(curs) DO
        IF lBrk THEN BuffEol; HTab; HTab END;
        GetNext(curs, parm); 
        EmitFormal(parm);
        IF NOT Ended(curs) THEN Comma END;
      END;
      WriteObjByte(")");
      BuffS(ilManaged); BuffEol;
    END EmitArgList;

  (* ================================================================= *)

    PROCEDURE PrologCopy(id : IdDesc);
    (*  This emits the code for expanding the copy area, for   *)
    (*  outgoing open array parameters that need marshalling.  *)
      VAR curs : ElemPtr;
          elem : IdDesc;
          mPtr : IdDesc;
          eTyp : TypeDesc;
          expd : ExpandInfo;
          nDim : CARDINAL;
          size : CARDINAL;
          indx : CARDINAL;
          temp : CARDINAL;
          argP : INTEGER;
          locP : INTEGER;
          mark : BOOLEAN;
          upLv : BOOLEAN;
          ptUp : BOOLEAN;
    BEGIN
      mark := FALSE;
      InitCursor(id^.body^.adjustSeq, curs);
      WHILE NOT Ended(curs) DO
        GetNext(curs, expd);
        WITH expd^ DO
          elem := mrshNode^.actualX^.name.variable;
          mPtr := mrshNode^.mrshPtr^.name.variable;
          nDim := dimenNum;
          size := elemType^.size;
          argP := parOrdinal(elem);
          locP := mPtr^.varOffset;
        END;
        mark := TRUE;
        upLv := inXSR(elem);
        ptUp := inXSR(mPtr);
        HTab; BuffS("// expand ("); BuffInt(nDim);
        BuffS("-D) for arg"); BuffInt(argP);
        BuffS(", ptr-loc:");   
        IF ptUp THEN BuffS("(&XSR)+") END; 
        BuffInt(locP);
        BuffS(", elem-sz=");  BuffCrd(size); BuffEol;
       (*
        *   emit the element count
        *)
        PushArgVal(argP+1); BuffEol; PushCrd(1); Add(none);
        FOR indx := 2 TO nDim DO
          PushArgVal(argP+INT(indx)); BuffEol; PushCrd(1); Add(none);
          Mul(none);
        END;
        IF size > 1 THEN PushCrd(size); Mul(none) END;
       (*
        *   allocate the space
        *)
        BuffI(opc_localloc); BuffEol;
        IF ptUp THEN
          temp := newTemp(PointerTo(adrs));
          StoreTemp(temp);
          PushLocalAdr(0); BuffEol;
          AddOffset(locP);
          PushTemp(temp);
          StoreInd(word); 
          FreeTemp(temp);
        ELSE
          StoreLocalVal(locP); BuffEol;
        END;
      END;

      IF hasXSR(id) THEN
        mark := TRUE;
       (*
        *  This proc has an explicit stack record (XSR)
        *)
        IF lexLevel(id) > 1 THEN (* nested proc *)
         (*
          *  Copy the static link to offset-0 in the XSR
          *)
          HTab; WriteComment("Copy static link to XSR");
          PushLocalAdr(0);     BuffEol;
          BuffI(opc_ldarg_0);  BuffEol;
          BuffI(opc_stind_i4); BuffEol;
        ELSE
         (*
          *  Upwards static link should be NIL
          *)
          HTab; WriteComment("Copy static link of NIL to XSR");
          PushLocalAdr(0);     BuffEol;
          BuffI(opc_ldnull);   BuffEol;
          BuffI(opc_stind_i4); BuffEol;
        END;
       (*
        *  Now copy any args that are uplevel addressed
        *)
        InitCursor(id^.exStRc^.fieldSeq, curs);
        GetNext(curs, elem);  (* this is the static pointer: discard *)
        WHILE NOT Ended(curs) DO
          GetNext(curs, elem); 
          IF elem^.hiDepth # notPar THEN
            HTab; WriteComment("Copy incoming arg to XSR field");
            eTyp := elem^.varType;
            PushLocalAdr(0);              BuffEol;
            AddOffset(elem^.varOffset);
            PushArgVal(elem^.hiDepth); BuffEol;
            StoreIndByType(eTyp);
          ELSE
          END;
        END;
      END;
      IF mark THEN HTab; WriteComment("End of prolog") END;
    END PrologCopy;

  (* ================================================================= *)

    PROCEDURE WrapperCopy(arg : INTEGER; siz : CARDINAL);
      VAR tmp : TempIndex;
    BEGIN
      tmp := newTemp(PointerTo(cards));
     (*
      *   Emit the element count, and calculate buffer size.
      *)
      PushArgVal(arg+1); BuffEol; PushCrd(1); Add(none);
      IF siz > 1 THEN PushCrd(siz); Mul(none) END;
      MakeTemp(tmp);
     (*
      *   allocate the space
      *)
      BuffI(opc_localloc); BuffEol;
      BuffI(opc_dup);      BuffEol;
      PushArgVal(arg);     BuffEol;
      PushTemp(tmp);
      CopyBlock(0C);
      FreeTemp(tmp);
      StoreArgVal(arg);    BuffEol;
    END WrapperCopy;

  (* ================================================================= *)

    PROCEDURE EmitWrapper();
      CONST argSave = "void [M2ClrRts]ProgArgs.ProgArgs::'__save'(string[])";
            mainStr = "::'.M2main'()";
            catchStr = "    catch  [mscorlib]System.Exception";
            exitLab  = "'ex$lb'";
            diagnose = "void [M2ClrRts]Traps::EmitExString";
            diagargs = "		    (class [mscorlib]System.Exception)";
    BEGIN
      WriteComment("Exception catch wrapper");
      BuffS(".method public static int32 '.CatchWrapper'");
      BuffS("(string[] args) il managed");   BuffEol;
      LBrace2;                               BuffEol;
      BuffS(".entrypoint");                  BuffEol;
      BuffS("  .try {");                     BuffEol;
      IF debugOn THEN LineNum(thisCompileUnit^.body^.headerLine) END;
      BuffI(opc_ldarg_0);                    BuffEol;
      BuffI(opc_call);      BuffS(argSave);  BuffEol;
      BuffI(opc_call);      BuffS("void ");
      BuffN(thisCompileUnit^.name);
      Dot;
      BuffN(thisCompileUnit^.name);
      BuffS(mainStr);                        BuffEol;
      IF debugOn THEN LineNum(thisCompileUnit^.body^.endIdLine) END;
      BuffI(opc_leave);     BuffS(exitLab);  BuffEol;
      RBrace2;                               BuffEol;
      BuffS(catchStr);                       BuffEol;
      LBrace2;                               BuffEol;
      BuffI(opc_call);  BuffS(diagnose);     BuffEol;
      BuffS(diagargs);                       BuffEol;
      BuffI(opc_ldc_i4_M1);                  BuffEol;
      BuffI(opc_stloc_0);                    BuffEol;
      BuffI(opc_leave); BuffS(exitLab);      BuffEol;
      RBrace2;                               BuffEol;
      BuffS(exitLab);   BuffS(":");          BuffEol;
      BuffI(opc_ldloc_0);                    BuffEol;
      BuffI(opc_ret);                        BuffEol;
      BuffS("  .locals init (int32 rVal)");  BuffEol;
      RBrace2; BuffS(" // end of wrapper");  BuffEol;
      BuffEol;
    END EmitWrapper;

  (* ================================================================= *)

    PROCEDURE EmitPInvoke(mod, fun : IdDesc);
    BEGIN
      BuffEol;
      BuffS("    .method assembly static pinvokeimpl(");
      WriteAsmNameFromSpix(mod^.libSpx, TRUE, '"');
      BuffS(" winapi)"); BuffEol;
      HTab;
      EmitResTypeName(fun^.procType^.result); Space;
      IF fun^.extAlias # 0 THEN
        WriteAsmNameFromSpix(fun^.extAlias, FALSE, "'");
      ELSE
        BuffN(fun^.name); 
      END;
      EmitParSig(fun^.procType, FALSE, TRUE);
      BuffS(" cil managed preservesig ");
      LBrace;            BuffEol;
      RBrace2;           BuffEol;
    END EmitPInvoke;

  (* ================================================================= *)

    PROCEDURE GenerateEntry(id : IdDesc);
    (* pre  : id has all info needed for stack frame generation *)
    (* post : proc state is evaluated, entry pseudo's emitted   *)
    (*        value arrays are copied and any soapspace fetched *)
      CONST argSave = "void [M2ClrRts]ProgArgs.ProgArgs::'__save'(string[])";
      VAR   name : HashBucketType;
            main : BOOLEAN;
    BEGIN
      BuffEol;
      InitCodeGen(id);                      (* And do indexing of locals *)
      ZeroStack;
      IF id^.idClass = modNode THEN
        main := (id = thisCompileUnit) AND (progMod IN modState); 
        BuffS(".method public ");
        IF main THEN
          BuffS("static void '.M2main'()")
        ELSE
          BuffS("specialname rtspecialname static void '.cctor'()")
        END;
        BuffS(ilManaged);
        BuffEol;
        LBrace2; BuffEol;
        IF debugOn THEN LineNum(id^.body^.headerLine) END;
      ELSIF id^.idClass = cilWrapper THEN
        BuffS("// Wrapper method"); BuffEol;
        WriteComment("");

        BuffS(".method ");
        EmitMethAttr(id); Space;
        BuffN(clrIdName(id));
        EmitCallSig(id); BuffEol;
        LBrace2; BuffEol;
      ELSE
        BuffS("// Reference name is "); BuffEol;
        BuffS("// ");
        EmitResTypeName(id^.procType^.result); Space;
        SetRetAdjust(id^.procType^.result # NIL);
        BuffH(clrRefName(id)); BuffS("(...)"); BuffEol;
        WriteComment("");

        BuffS(".method ");
        EmitMethAttr(id); Space;
        BuffN(clrIdName(id));
        EmitArgList(id);         (* creates argument list *)
        LBrace2; 
        BuffS("  // lexical level "); BuffCrd(lexLevel(id));
        BuffEol;
        IF debugOn THEN LineNum(id^.body^.headerLine) END;
        PrologCopy(id);
      END;
    END GenerateEntry;

  (* ================================================================= *)

    PROCEDURE GenerateExit(id : IdDesc);
    BEGIN
      MaxStack();
      EmitLocals(id);
      RBrace2; BuffEol;
      ResetCodeGen;
    END GenerateExit;

  (* ================================================================= *)

    PROCEDURE ClassBegin(nam : HashBucketType);
    BEGIN
      BuffEol;
      WriteComment("Start of synthetic static class");
      BuffS(".class public sealed "); BuffN(nam); LBrace; BuffEol;
    END ClassBegin;

  (* ================================================================= *)

    PROCEDURE ClassEnd(nam : HashBucketType);
    BEGIN
      BuffS("} // End of synthetic static class "); BuffN(nam); BuffEol;
      BuffEol;
    END ClassEnd;

  (* ================================================================= *)

   (* This fn. returns the name of the entrypoint/initialization entry *)
    PROCEDURE callSmbl() : HashBucketType;
    BEGIN
      IF progMod IN modState THEN RETURN catchBkt ELSE RETURN cctorBkt END;
    END callSmbl;

BEGIN
  aliasInf := FALSE; (* just a dummy *)
END M2CILwriter.

