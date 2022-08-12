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
	:	LPAREN FORALL LPAREN paramDecls=declList RPAREN op=quantifiedExpr RPAREN
	;

existsExpr
	:	LPAREN EXISTS LPAREN paramDecls=declList RPAREN op=quantifiedExpr RPAREN
	;

fpFuncExpr
    :   leftOp=orExpr
    |   LPAREN oper=(FPMAX | FPMIN) leftOp=orExpr rightOp=orExpr RPAREN
    ;

orExpr
    :   xorExpr
	|	LPAREN OR ops+=xorExpr (ops+=xorExpr)* RPAREN
	;

xorExpr
    :   andExpr
	|	LPAREN XOR leftOp=andExpr rightOp=xorExpr RPAREN
	;

andExpr
    :   notExpr
	|	LPAREN AND ops+=notExpr (ops+=notExpr)* RPAREN
	;

notExpr
	:	equalityExpr
	|	LPAREN NOT op=equalityExpr RPAREN
	;

equalityExpr
    :   relationExpr
	|	LPAREN oper=(EQ | NEQ) leftOp=relationExpr rightOp=relationExpr RPAREN
	;

relationExpr
    :   bitwiseOrExpr
	|	LPAREN oper=(LT | LEQ | GT | GEQ | BV_ULT | BV_ULE | BV_UGT | BV_UGE | BV_SLT | BV_SLE | BV_SGT | BV_SGE) leftOp=bitwiseOrExpr rightOp=bitwiseOrExpr RPAREN
	;

bitwiseOrExpr
    :   bitwiseXorExpr
    |   LPAREN oper=BV_OR leftOp=bitwiseXorExpr rightOp=bitwiseXorExpr RPAREN
    ;

bitwiseXorExpr
    :   bitwiseAndExpr
    |   LPAREN oper=BV_XOR leftOp=bitwiseAndExpr rightOp=bitwiseAndExpr RPAREN
    ;

bitwiseAndExpr
    :   bitwiseShiftExpr
    |   LPAREN oper=BV_AND leftOp=bitwiseShiftExpr rightOp=bitwiseShiftExpr RPAREN
    ;

bitwiseShiftExpr
    :   additiveExpr
    |   LPAREN oper=(BV_SHL | BV_ASHR | BV_LSHR | BV_ROL | BV_ROR) leftOp=additiveExpr rightOp=additiveExpr RPAREN
    ;

additiveExpr
    :   multiplicativeExpr
	|	LPAREN oper=(PLUS | MINUS | BV_ADD | BV_SUB | FPADD | FPSUB) ops+=multiplicativeExpr (ops+=multiplicativeExpr)* RPAREN
	;

multiplicativeExpr
    :   bvConcatExpr
	|	LPAREN oper=(MUL | DIV | MOD | REM | BV_MUL | BV_UDIV | BV_SDIV | BV_SMOD | BV_UREM | BV_SREM | FPREM | FPMUL | FPDIV) ops+=bvConcatExpr (ops+=bvConcatExpr)* RPAREN
	;

bvConcatExpr
    :   bvExtendExpr
    |   LPAREN oper=BV_CONCAT (ops+=bvExtendExpr)+ RPAREN
    ;

bvExtendExpr
    :   unaryExpr
    |   LPAREN oper=(BV_ZERO_EXTEND | BV_SIGN_EXTEND) leftOp=unaryExpr rightOp=bvType RPAREN
    ;

unaryExpr
	:	bitwiseNotExpr
	|	LPAREN oper=(PLUS | MINUS | BV_POS | BV_NEG | FP_ABS | FP_IS_NAN | FPROUNDTOINT | FPSQRT | FPTOFP | FPTOBV | FP_FROM_BV | FPNEG | FPPOS ) op=unaryExpr RPAREN
	;

bitwiseNotExpr
    :   functionCall
    |   LPAREN BV_NOT op=bitwiseNotExpr RPAREN
    ;

functionCall
    :   arrayRead
    |   LPAREN FUNC op=primaryExpr (ops+=primaryExpr)* RPAREN
    ;

arrayRead
    :   arrayWrite
    |   LPAREN READ array=primaryExpr index=primaryExpr RPAREN
    ;

arrayWrite
    :   primeExpr
    |   LPAREN WRITE array=primaryExpr index=primaryExpr elem=primaryExpr RPAREN
    ;

primeExpr
    :   bvExtract
    |   LPAREN PRIME op=primaryExpr RPAREN
    ;

bvExtract
    :   primaryExpr
    |   LPAREN EXTRACT op=primaryExpr from=intLitExpr until=intLitExpr RPAREN
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
	:	oper=(PLUS | MINUS)? value=INT
	;

ratLitExpr
	:	oper=(PLUS | MINUS)? num=INT PERCENT denom=INT
	;

arrLitExpr
    :   LPAREN ARRAY (LPAREN indexExpr+=expr valueExpr+=expr RPAREN)* LPAREN DEFAULT elseExpr=expr RPAREN RPAREN
    ;

bvLitExpr
    :   bv=BV
    ;

fpLitExpr
    :   LPAREN bvLitExpr bvLitExpr bvLitExpr RPAREN
    ;

idExpr
	:	id=ID
	;

parenExpr
	:	LPAREN op=expr RPAREN
	;
