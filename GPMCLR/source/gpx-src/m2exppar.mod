(****************************************************************)
(*                                                              *)
(*              Modula-2 Compiler Source Module                 *)
(*								*)
(*            Expression Parser and Tree Constructor.           *)
(*								*)
(*    (c) copyright 1987 Faculty of Information Technology      *)
(*								*)
(*      original module : extracted from M2Parser April 1988    *)
(*      modifications   : 31-Aug-88 improve error 203 reports   *)
(*                        07-Nov-88 improve error 201 reports   *)
(*                        22-Feb-89 new error 135 added         *)
(*			  26-Feb-89 kjg, recovery in ranges     *)
(*			  26-Jun-89 jrh, add remSy to mulops    *)
(*			  23-Sep-89 kjg, use CopyEnums		*)
(*			   9-Nov-89 kjg, parsing constructors   *)
(*			  12-Jun-90 kjg  charNums compat. to S1 *)
(*			   6-Jul-90 kjg  uses new parser syncs  *)
(*			  13-Jul-90 kjg  new Insert mutatis mut *)
(*			  20-Jul-90 kjg  use new ConstAssignCom *)
(*			  12-May-92 kjg  const can be fwd proc	*)
(*			  14-May-92 jrh  QualRest fwdMod	*)
(*                                                              *)
(****************************************************************
$Log: m2exppar.mod,v $
Revision 1.5  1997/01/16 03:44:26  gough
new procedure PreCondition
Symbol file opening and closing procedures are now changed, so sthat
symbol file parsing can be re-entrant. A final call to BindAllFields
replaces the ImportAliasModules call, which has become redundant.

Revision 1.4  1995/10/10 23:21:31  lederman
ConstAssignCompatible no longer exported by m2ssutil

# Revision 1.3  1994/10/18  07:31:02  gough
# protect call of TraverseExp in ConstExpr with <no errors> test
#
# Revision 1.2  1994/07/01  04:33:21  lederman
# set type = NIL on error in ConstExpr - caused FOR with non-lit step to crash
#
# Revision 1.1  1994/04/07  04:52:45  lederman
# Initial revision
#
*****************************************************************
Revision 1.4  94/03/28  14:45:05  lederman
removed reference to Convert

Revision 1.3  94/03/21  13:30:42  gough
fix up constant expressions with function name values
*****************************************************************)

IMPLEMENTATION MODULE M2ExpParser;

(* IMPORT HeapMonitor; *)

IMPORT StdError;
IMPORT Storage, SYSTEM;

FROM M2NodeDefs  IMPORT 
	IdDesc, IdTree, IdNodeClass, CreateIdDesc, InsertRef, 
	TypeDesc, TyNodeClass, StandardProcs,
	FormalType, FormalClass, FormalRec, MakeFormal, modState,
	globalModList, thisCompileUnit, pervasiveUnit, current,
	SuspendList, ResumeList, TyClassSet, IdClassSet;

FROM M2StructureDefs IMPORT 
	RangeDesc, RangeRec, MakeRangeDesc,
	CaseStatDesc, CaseStatRec, CaseDesc, CaseRec;

FROM M2Designators IMPORT
	ExprNodeClass, ExprDesc, ExprRec, CreateExprDesc,
	InitDesignator, DesigRec, SelectNodeClass, ParseDesignator;

FROM M2Alphabets IMPORT  
	TerminalSymbols, SymbolSet, Spellix,
	ModStateFlags, ModStateSet, errors,
	HashBucketType, Flags, FlagSet, LexAttType, ConBlock;

FROM M2Scanner   IMPORT 
	(* CurrentFlags,*) 
	symbol, lexAtt, GetSymbol, SetFlagOn, StartSyncCount;

FROM M2NameHandler IMPORT 
	(* set operations *) Commit,
	anonBkt, MakeEmptySet, SetInclude, SetRngIncl;

FROM M2InOut IMPORT 
DiagName,
	OpenOldSymFile, CloseOldSymFile, ErrIdent, Error, lastPos;

FROM M2SymParser IMPORT 
	librarySpx, ParseSymbolFile, BindAllFields, CopyEnums;

FROM GenSequenceSupport IMPORT 
	Sequence, ElemPtr, LinkLeft,
	LinkRight, InitCursor, GetNext,
	InitSequence, NextIsLast, Ended,
	DisposeList;

FROM M2SSUtilities IMPORT 
	Lookup, LookupAndMarkUplevel, 
	LookupInThisScope, LookupInModList,
	OrdinalValue, Compatible, IsSignedType,
	MinOfOrdType, MaxOfOrdType, FixTypeAndValue,
	IndexCardinality, IsOrdinalType, IsOwnOpaque;

FROM M2CompOperations IMPORT 
	Operation, Negate, ExtractCon, CopyConstant;

FROM M2TabInitialize IMPORT PointerTo;

FROM M2MachineConstants IMPORT 
	bitsInWord, bytesInWord, cardMax,
	nilValue, maxSetCard, charMax, intMax;

FROM M2Traversal     IMPORT TraverseExp;

FROM ProgArgs IMPORT Assert;

(****************************************************************)

    CONST   relops   = SymbolSet{equals, notEq, greater,
                              grEqual, less, lessEq, inSy};
            mulops   = SymbolSet{andSy, divSy, star, slash, modSy, remSy};
            addops   = SymbolSet{plus, minus, orSy};
            firstExp = SymbolSet{plus, minus, notSy, lPar, ident,
                                 charLit, litstring, fixNum,
                                 charNum, floatNum, nilSy};
            idSet    = SymbolSet{ident};
            semiSet  = SymbolSet{semi};
            eofSet   = SymbolSet{eofSy};
            commaSet = SymbolSet{comma};

    CONST followDefs   = SymbolSet{ varSy, endSy, constSy,
                                     typeSy, procedureSy };
          followDecs   = followDefs + SymbolSet{beginSy, moduleSy };
          followImport = followDecs + 
                           SymbolSet{importSy, exportSy, fromSy };
          exitSet      = semiSet + eofSet + followImport;

          puncSyms     = SymbolSet{comma,semi,colon,equals,assignSy};

    CONST conClasses  = TyClassSet{sets, records, arrays};

    TYPE  StProcSet   = SET OF StandardProcs;

    PROCEDURE SkipTo(haltSet : SymbolSet; errNo : CARDINAL);
    BEGIN
      IF NOT (symbol IN haltSet) THEN
         IF errNo <> 0 THEN 
	   Error(errNo);
         END;
         INCL(haltSet,eofSy);
         WHILE NOT (symbol IN haltSet) DO GetSymbol END;
	 IF errNo <> 0 THEN 
	   StartSyncCount();
	 END;
      END;
    END SkipTo; (* post : symbol is in haltSet + {eofSy} *)

    PROCEDURE ErrSkip(haltSet : SymbolSet; errNo : CARDINAL);
    BEGIN
      Error(errNo);
      INCL(haltSet,eofSy); 
      WHILE NOT (symbol IN haltSet) DO GetSymbol END;
      (* start countdown to indicate synchronization *)
      StartSyncCount();
    END ErrSkip; (* post : symbol is in haltSet + {eofSy} *)

    PROCEDURE Error203(old : IdDesc);
    (* check if the clashing ident is actually an enum
       constant. If so ... give a specific error message *)
      VAR num : CARDINAL;
    BEGIN
      IF  (old^.idClass = constNode) AND
          (old^.conType <> NIL) AND
          (old^.conType^.tyClass = enums) THEN num := 266;
      ELSE num := 203;
      END;
      (* if symbol not ident then identify name *)
      IF symbol = ident THEN Error(num);
      ELSE ErrIdent(num,old^.name);
      END;
    END Error203;

(****************************************************************)

    PROCEDURE Qualident(VAR obj : IdDesc);
    (* returns the ident designated, or NIL for error *)
    (* postcondition : either id = NIL, or id designates one of:
                       entire variable, constant, type or proc. *)
      VAR hsh : HashBucketType;
    BEGIN 
      Assert(symbol = ident);
      hsh := lexAtt.hashIx; GetSymbol;
      QualRest(hsh,obj);
    END Qualident;

    PROCEDURE QualRest(hsh : HashBucketType;
                    VAR id : IdDesc);
    BEGIN
      LookupAndMarkUplevel(hsh,id);
      (* no error message -- caller raises error *)
      WHILE (id <> NIL) AND (id^.idClass IN IdClassSet{exportNode,fwdMod}) 
             AND (symbol = dot) DO
        GetSymbol;
        IF symbol = ident THEN
          LookupInThisScope(id^.exports,lexAtt.hashIx,id);
          GetSymbol;
        ELSE id := NIL; Error(108);
        END;
      END;
    END QualRest;

(****************************************************************)

    PROCEDURE PreCondition(pTyp : TypeDesc);
      CONST halt = followDefs + semiSet;
      VAR   expr : ExprDesc;
    BEGIN
      GetSymbol; (* discard preconSy *)
      Expression(halt,expr);
      pTyp^.preCon := expr;
      IF symbol = semi THEN GetSymbol;
      ELSE ErrSkip(followDefs,121);
      END;	
    END PreCondition;

(****************************************************************)

    PROCEDURE ConstExpr(halt : SymbolSet;
                      VAR type : TypeDesc;
                      VAR cVal : LexAttType);
      VAR expr : ExprDesc;
   (* ------------------------------------------------ *)
    BEGIN (* ConstExpr = SimpleExpr [relop SimpleExpr] *)
      Expression(halt,expr);
(*
 *    IF errors * CurrentFlags() <> FlagSet{} THEN 
 *	type := NIL;
 *    ELSE 
 *)
      IF expr <> NIL THEN 
	TraverseExp(expr);
      END;
      IF expr <> NIL THEN 
        IF expr^.exprClass = literalNode THEN
	  type := expr^.exprType;
	  cVal := expr^.conValue;
	ELSIF (expr^.exprClass = desigNode) AND
	      (expr^.exprType <> NIL) AND
	      ((expr^.exprType^.tyClass = procTypes) OR
	       (expr^.exprType^.tyClass = funcTypes)) THEN
	  type := PointerTo(procTypes);
	  cVal.adrsValue := expr^.name.variable;
	ELSE
	  Error(208); type := NIL;
 	END;
      END;
    END ConstExpr;

    PROCEDURE GetCaseRange(halt : SymbolSet;
                       VAR sequ : Sequence); (* of case ranges *)
      VAR new : SymbolSet;
          left, right : ExprDesc;
    BEGIN
      new := halt; INCL(new,dotDot);
      CreateExprDesc(left,literalNode);
      ConstExpr(new,left^.exprType,left^.conValue);
      SkipTo(new,110); (* expected comma *)
      IF symbol = dotDot THEN
        GetSymbol;
        CreateExprDesc(right,literalNode);
        ConstExpr(new,right^.exprType,right^.conValue);
        LinkRight(sequ,MakeRangeDesc(left,right));
      ELSE LinkRight(sequ,MakeRangeDesc(left,left));
      END;
    END GetCaseRange;

    PROCEDURE ImportOwnSyms;
      VAR ok : BOOLEAN;
    BEGIN
      OpenOldSymFile(thisCompileUnit^.name,ok);
      IF ok THEN ParseSymbolFile(thisCompileUnit)
      ELSE
        ErrIdent(201,thisCompileUnit^.name);
        SetFlagOn(filErrors);
      END;
      CloseOldSymFile();
    END ImportOwnSyms;

  PROCEDURE ActualParams(halt : SymbolSet;
                     VAR sequ : Sequence);
    VAR new, restart, exitSyms : SymbolSet;
        exp : ExprDesc;
  BEGIN
    new := halt + commaSet;
    exitSyms := halt - puncSyms;
    restart := firstExp + commaSet + exitSyms;
    LOOP
      IF symbol IN firstExp THEN
        Expression(new,exp);
        LinkRight(sequ,exp);
      ELSE Error(120);
      END;
      IF symbol = comma THEN GetSymbol;
      ELSIF symbol IN exitSyms THEN EXIT;
      ELSE ErrSkip(restart,110);
      END;
    END;
    SkipTo(halt,111);
  END ActualParams;

  PROCEDURE Expression(halt : SymbolSet;
                   VAR expr : ExprDesc);

    PROCEDURE SimpleExpression(halt : SymbolSet;
                           VAR expr : ExprDesc);

      PROCEDURE Term(halt : SymbolSet;
                 VAR expr : ExprDesc);

        PROCEDURE Factor(halt : SymbolSet;
                     VAR expr : ExprDesc);

          PROCEDURE GetRanges(halt : SymbolSet;
                          VAR sequ : Sequence);
            VAR first, second, restart : SymbolSet;
                left, right   : ExprDesc;
		countTyp      : TypeDesc;
		countVal      : LexAttType;
          BEGIN
            second  := halt + commaSet;
            first   := second + SymbolSet{dotDot,bySy};
            restart := second + firstExp;
            LOOP
              IF (symbol = lCurly) OR (symbol IN firstExp) THEN
		IF symbol = lCurly THEN (* anon constructor *)
		  GetSymbol;
		  CreateExprDesc(left,constructorNode);
		  InitSequence(left^.rangeSeq);
		  InitDesignator(left^.name);
		  IF symbol <> rCurly THEN 
		    GetRanges(halt,left^.rangeSeq);
		  END;
		  IF symbol = rCurly THEN GetSymbol ELSE Error(122) END;
		ELSE Expression(first,left);
		END;
                SkipTo(first,110); (* expected comma *)
                IF symbol = dotDot THEN
                  GetSymbol;
                  Expression(second,right);
		ELSIF symbol = bySy THEN (* do replicator *)
		  GetSymbol;
		  ConstExpr(second,countTyp,countVal);
		  IF NOT Compatible(countTyp,PointerTo(cards)) OR
				     (countVal.fixValue = 0) THEN (* Oct 92 *)
		    Error(317); (* "must be positive const " *)
		  END;
		  CreateExprDesc(right,repCountNode);
		  right^.count := countVal.fixValue;
                ELSE right := NIL;
                END;
                LinkRight(sequ,MakeRangeDesc(left,right));
              ELSE Error(120);
              END;
              IF symbol = comma THEN GetSymbol;
              ELSIF symbol IN halt THEN EXIT;
              ELSE ErrSkip(restart,110);
              END;
            END;
            SkipTo(halt,122);
          END GetRanges;

          VAR new : SymbolSet;
              tag : TyNodeClass;
        BEGIN (* factor *)
          IF symbol = ident THEN
            CreateExprDesc(expr,desigNode);
            new := halt + SymbolSet{lPar,lCurly};
            ParseDesignator(new,expr^.name);
            IF symbol = lPar THEN (* function application *)
              expr^.exprClass := funcDesigNode;
              InitSequence(expr^.paramSeq);
              GetSymbol;
              IF symbol <> rPar THEN
                new := halt; INCL(new,rPar);
                ActualParams(new,expr^.paramSeq);
                IF symbol = rPar THEN GetSymbol;
                ELSE Error(111);
                END;
              ELSE GetSymbol;
              END;
            ELSIF symbol = lCurly THEN (* set constructor *)
              expr^.exprClass := constructorNode;
              InitSequence(expr^.rangeSeq);
              GetSymbol;
              IF symbol <> rCurly THEN
                new := halt + SymbolSet{rCurly};
                GetRanges(new,expr^.rangeSeq);
                IF symbol = rCurly THEN GetSymbol;
                ELSE Error(122);
                END;
              ELSE GetSymbol;
              END;
            END;
          ELSIF symbol = lPar THEN
            GetSymbol;
            new := halt; INCL(new,rPar);
            Expression(new,expr);
            IF symbol = rPar THEN GetSymbol;
            ELSE Error(111);
            END;
          ELSIF symbol = notSy THEN
            CreateExprDesc(expr,notNode); GetSymbol;
            Factor(halt,expr^.notOp);
          ELSIF symbol IN SymbolSet{nilSy,litstring..charNum} THEN
            CreateExprDesc(expr,literalNode);
            expr^.conValue := lexAtt;
            CASE symbol OF
              litstring : tag := SS;
            | floatNum  : tag := RR;
            | charLit   : tag := S1;
            | charNum   : tag := S1;	(* 12-Jun previously chars *)
            | nilSy     : tag := adrs;
                          expr^.conValue.adrsValue := nilValue;
            | fixNum    : IF lexAtt.fixValue > intMax THEN tag := UU;
                          ELSE tag := ZZ;
                          END;
            END;
            expr^.exprType := PointerTo(tag);
            GetSymbol;
          ELSE Error(135); expr := NIL;
          END;
          SkipTo(halt,120);
        END Factor;

        VAR left : ExprDesc;
            new  : SymbolSet;
      BEGIN (* term *)
        new := halt + mulops;
        Factor(new,expr);
        WHILE symbol IN mulops DO
          left := expr;
          CreateExprDesc(expr,VAL(ExprNodeClass,ORD(symbol)));
          GetSymbol;
          expr^.leftOp := left;
          Factor(new,expr^.rightOp);
        END;
        SkipTo(halt,127);
      END Term;

      VAR left  : ExprDesc;
          new   : SymbolSet;
          isNeg : BOOLEAN;
    BEGIN (* simple expression *)
      new := halt + addops;
      IF symbol = minus THEN
        CreateExprDesc(expr,negateNode); GetSymbol;
        Term(new,expr^.notOp);
      ELSE
        IF symbol = plus THEN GetSymbol END;
        Term(new,expr);
      END;
      WHILE symbol IN addops DO
        left := expr;
        CreateExprDesc(expr,VAL(ExprNodeClass,ORD(symbol)));
        GetSymbol;
        expr^.leftOp := left;
        Term(new,expr^.rightOp);
      END;
      SkipTo(halt,126);
    END SimpleExpression;

    VAR left : ExprDesc;
        new  : SymbolSet;
  BEGIN (* expression *)
    new := halt + relops;
    SimpleExpression(new,expr);
    IF symbol IN relops THEN
      left := expr;
      CreateExprDesc(expr,VAL(ExprNodeClass,ORD(symbol)));
      GetSymbol;
      expr^.leftOp := left;
      SimpleExpression(halt,expr^.rightOp);
    END;
  END Expression;

    PROCEDURE CompImports; (* for compilation units only *)
      CONST  starters  = SymbolSet{fromSy,importSy};
             enders    = followImport;
             restart   = idSet + exitSet + commaSet;

      VAR needsHdrSpx  : BOOLEAN;

      PROCEDURE SeekModule(hash : HashBucketType;
                       VAR newMod : IdDesc;
                            VAR ok : BOOLEAN);
      BEGIN
(**)    LookupInModList(hash,newMod);
        IF newMod = NIL THEN (* module is not known yet *)
          CreateIdDesc(hash,newMod,exportNode);
          OpenOldSymFile(hash,ok);
          IF ok THEN
            ParseSymbolFile(newMod);
            LinkRight(globalModList,newMod);
          ELSE SetFlagOn(filErrors);
          END;
	  CloseOldSymFile();
        ELSIF NOT newMod^.loaded THEN (* known but not loaded *)
          OpenOldSymFile(hash,ok);
          IF ok THEN ParseSymbolFile(newMod);
          ELSE SetFlagOn(filErrors);
          END;
	  CloseOldSymFile();
        ELSE (* sym file already loaded *)
          ok := TRUE;
(**)    END;
      END SeekModule;

      PROCEDURE Import;
         VAR   symFileOK, ok : BOOLEAN;
               modPtr, objPtr, existing : IdDesc;
               hsh : HashBucketType; curs : ElemPtr;
	       sym : TerminalSymbols;
      BEGIN (* assert: symbol in starters *)
      (* Import = [fromSy ident] importSy IdentList semi.    *)
      (* HrdImp = importSy implementationSy fromSy litString.*)
         IF symbol = fromSy THEN
           GetSymbol;
           IF symbol <> ident THEN ErrSkip(idSet + enders,108) END;
           IF symbol = ident THEN
             hsh := lexAtt.hashIx; GetSymbol;
             SeekModule(hsh,modPtr,symFileOK);
             IF symFileOK THEN
(* just experimental *)
(*
               InsertRef(current^.scope,modPtr,ok);
 *)
(* end experimental *)
               (* symbol file, modPtr^, is now loaded *)
               IF symbol = importSy THEN GetSymbol;
               ELSE (* expected import *)
                  ErrSkip(exitSet,109);
                  IF symbol = importSy THEN GetSymbol END;
               END;

               LOOP
                  IF symbol = ident THEN (* copy to current scope *)
                    hsh := lexAtt.hashIx;
                    LookupInThisScope(modPtr^.scope,hsh,objPtr);
                    IF objPtr = NIL THEN (* not exported *)
                      Error(202);
                    ELSE (* if not already present ... *)
                      InsertRef(current^.scope,objPtr,ok);
                      IF NOT ok THEN (* what caused the clash? *)
                        LookupInThisScope(current^.scope,hsh,existing);
			Error203(existing);
                      ELSIF (objPtr^.idClass = typeNode) AND
                             (objPtr^.typType^.tyClass = enums) THEN
			CopyEnums(current,objPtr^.typType^.conSeq);
                      END;
                    END; (* if exported *)
                    GetSymbol;
                  ELSE ErrSkip(restart,108);
                  END;
                  IF symbol = comma THEN GetSymbol;
                  ELSIF symbol IN exitSet THEN EXIT;
                  ELSE
                    ErrSkip(restart,110);
                    IF symbol IN exitSet THEN EXIT END;
                  END;
               END; (* loop *)
             ELSE ErrSkip(semiSet,201);
             END; (* of symFile is OK *)
           END; (* if symbol = ident *)
         ELSE (* symbol = importSy *)
           GetSymbol;
	   IF (symbol = implementationSy) AND needsHdrSpx THEN
	     GetSymbol; (* implementationSy *)
	     sym := symbol; GetSymbol;
	     IF (sym <> fromSy) OR (symbol <> litstring) THEN
	       ErrSkip(restart,140);
	     ELSE 
	       librarySpx := lexAtt.stringIx; 
	       needsHdrSpx := FALSE;
	       GetSymbol;
	     END;
	   ELSE
             LOOP
               IF symbol = ident THEN
                 hsh := lexAtt.hashIx;
                 SeekModule(hsh,modPtr,symFileOK);
                 (* this places all symbols in the tree for this
                     module in the global module list. Now "import" *)
                 IF symFileOK THEN
                    InsertRef(current^.scope,modPtr,ok);
                    IF NOT ok THEN
                      LookupInThisScope(current^.scope,hsh,objPtr);
                      Error203(objPtr);
                    END;
                 ELSE Error(201);
                 END;
                 GetSymbol; (* ident *)
               ELSE ErrSkip(restart,108);
               END;
               IF symbol = comma THEN GetSymbol;
               ELSIF symbol IN exitSet THEN EXIT;
               ELSE 
                 ErrSkip(restart,110);
                 IF symbol IN exitSet THEN EXIT END;
               END;
             END; (* loop *)
	   END;
         END; (* if *)
         (* assert: sym IN {semi,eofSy} + followImport *)
         IF symbol = semi THEN GetSymbol;
         ELSE Error(105);
         END;
      END Import; (* last was semi, OR sym in followImport + {eofSy} *)

    BEGIN
      librarySpx  := 0;
      needsHdrSpx := (macroMod IN modState);
      LOOP
         IF symbol IN starters THEN Import;
         ELSIF symbol IN exitSet (* - starters *) THEN EXIT;
         ELSE ErrSkip(followImport, 106);
         END;
      END;
      BindAllFields(); (* modules indirectly imported *)
      (* HeapMonitor.Stop(HeapMonitor.use2); *)
    END CompImports;

END M2ExpParser.
