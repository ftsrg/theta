grammar Expr;

import Declarations;

expr:	funcLitExpr
	;

exprList
	:	(exprs+=expr)(COMMA exprs+=expr)*
	;

funcLitExpr
	:	iteExpr
	|	LPAREN FUNC param=decl result=funcLitExpr RPAREN
	;

iteExpr
	:	iffExpr
	|	LPAREN ITE cond=expr then=expr elze=iteExpr RPAREN
	;

iffExpr
    :   implyExpr
	|	LPAREN IFF leftOp=implyExpr (rightOp=iffExpr)? RPAREN
	;

implyExpr
    :   quantifiedExpr
	|	LPAREN IMPLY leftOp=quantifiedExpr (rightOp=implyExpr)? RPAREN
	;

quantifiedExpr
	:	fpFuncExpr
	|	forallExpr
	|	existsExpr
	;

forallExpr
	:	FORALL LPAREN paramDecls=declList RPAREN op=quantifiedExpr
	;

existsExpr
	:	EXISTS LPAREN paramDecls=declList RPAREN op=quantifiedExpr
	;

fpFuncExpr
    :   leftOp=orExpr (oper=(FPMAX | FPMIN) rightOp=orExpr)?
    ;

orExpr
	:	ops+=xorExpr (OR ops+=xorExpr)*
	;

xorExpr
	:	leftOp=andExpr (XOR rightOp=xorExpr)?
	;

andExpr
	:	ops+=notExpr (AND ops+=notExpr)*
	;

notExpr
	:	equalityExpr
	|	NOT op=equalityExpr
	;

equalityExpr
	:	leftOp=relationExpr (oper=(EQ | NEQ) rightOp=relationExpr)?
	;

relationExpr
	:	leftOp=bitwiseOrExpr (oper=(LT | LEQ | GT | GEQ | BV_ULT | BV_ULE | BV_UGT | BV_UGE | BV_SLT | BV_SLE | BV_SGT | BV_SGE) rightOp=bitwiseOrExpr)?
	;

bitwiseOrExpr
    :   leftOp=bitwiseXorExpr (oper=BV_OR rightOp=bitwiseXorExpr)?
    ;

bitwiseXorExpr
    :   leftOp=bitwiseAndExpr (oper=BV_XOR rightOp=bitwiseAndExpr)?
    ;

bitwiseAndExpr
    :   leftOp=bitwiseShiftExpr (oper=BV_AND rightOp=bitwiseShiftExpr)?
    ;

bitwiseShiftExpr
    :   leftOp=additiveExpr (oper=(BV_SHL | BV_ASHR | BV_LSHR | BV_ROL | BV_ROR) rightOp=additiveExpr)?
    ;

additiveExpr
	:	ops+=multiplicativeExpr (opers+=(PLUS | MINUS | BV_ADD | BV_SUB | FPADD | FPSUB) ops+=multiplicativeExpr)*
	;

multiplicativeExpr
	:	ops+=bvConcatExpr (opers+=(MUL | DIV | MOD | REM | BV_MUL | BV_UDIV | BV_SDIV | BV_SMOD | BV_UREM | BV_SREM | FPREM | FPMUL | FPDIV) ops+=bvConcatExpr)*
	;

bvConcatExpr
    :   ops+=bvExtendExpr (opers+=BV_CONCAT ops+=bvExtendExpr)*
    ;

bvExtendExpr
    :   leftOp=unaryExpr (oper=(BV_ZERO_EXTEND | BV_SIGN_EXTEND) rightOp=bvType)?
    ;

unaryExpr
	:	bitwiseNotExpr
	|	oper=(PLUS | MINUS | BV_POS | BV_NEG | FP_ABS | FP_IS_NAN | FPROUNDTOINT | FPSQRT | FPTOFP | FPTOBV | FP_FROM_BV | FPNEG | FPPOS ) op=unaryExpr
	;

bitwiseNotExpr
    :   accessorExpr
    |   BV_NOT op=bitwiseNotExpr
    ;

accessorExpr
	:	op=primaryExpr (accesses+=access)*
	;

access
	:	params=funcAccess
	|	readIndex=arrayReadAccess
	|	writeIndex=arrayWriteAccess
	|	prime=primeAccess
	|   bvExtract=bvExtractAccess
	;

funcAccess
	:	LPAREN (params=exprList)? RPAREN
	;

arrayReadAccess
	:	LBRACK index=expr RBRACK
	;

arrayWriteAccess
	:	LBRACK index=expr LARROW elem=expr RBRACK
	;

primeAccess
	:	QUOT
	;

bvExtractAccess
    :   LBRACK until=INT COLON from=INT RBRACK
    ;

primaryExpr
	:	trueExpr
	|	falseExpr
	|	intLitExpr
	|	ratLitExpr
	|	arrLitExpr
	|   fpLitExpr
	|	bvLitExpr
	|	idExpr
	|	parenExpr
	;

trueExpr
	:	TRUE
	;

falseExpr
	:	FALSE
	;

intLitExpr
	:	value=INT
	;

ratLitExpr
	:	num=INT PERCENT denom=INT
	;

arrLitExpr
    :   LBRACK (indexExpr+=expr LARROW valueExpr+=expr COMMA)+ (LT indexType=type GT)? DEFAULT LARROW elseExpr=expr RBRACK
    |   LBRACK LT indexType=type GT DEFAULT LARROW elseExpr=expr RBRACK
    |   LPAREN ARRAY (LPAREN indexExpr+=expr valueExpr+=expr RPAREN)* LPAREN DEFAULT elseExpr=expr RPAREN RPAREN
    ;

bvLitExpr
    :   bv=BV
    ;

fpLitExpr
    :   sig=(PLUS | MINUS)? bvLitExpr DOT bvLitExpr
    ;

idExpr
	:	id=ID
	;

parenExpr
	:	LPAREN op=expr RPAREN
	;
