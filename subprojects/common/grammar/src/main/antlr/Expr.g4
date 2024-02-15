grammar Expr;

import Declarations;

expr:	funcLitExpr
	;

exprList
	:	(exprs+=expr)(COMMA exprs+=expr)*
	;

funcLitExpr
	:	iteExpr
	|	LPAREN FUNC param=decl result=expr RPAREN
	;

iteExpr
	:	iffExpr
	|	LPAREN ITE cond=expr then=expr elze=expr RPAREN
	;

iffExpr
    :   implyExpr
	|	LPAREN IFF leftOp=expr (rightOp=expr)? RPAREN
	;

implyExpr
    :   quantifiedExpr
	|	LPAREN IMPLY leftOp=expr (rightOp=expr)? RPAREN
	;

quantifiedExpr
	:	fpFuncExpr
	|	forallExpr
	|	existsExpr
	;

forallExpr
	:	LPAREN FORALL LPAREN paramDecls=declList RPAREN op=expr RPAREN
	;

existsExpr
	:	LPAREN EXISTS LPAREN paramDecls=declList RPAREN op=expr RPAREN
	;

fpFuncExpr
    :   orExpr
    |   LPAREN oper=(FPMAX | FPMIN) leftOp=expr rightOp=expr RPAREN
    ;

orExpr
    :   xorExpr
	|	LPAREN OR ops+=expr (ops+=expr)* RPAREN
	;

xorExpr
    :   andExpr
	|	LPAREN XOR leftOp=expr rightOp=expr RPAREN
	;

andExpr
    :   notExpr
	|	LPAREN AND ops+=expr (ops+=expr)* RPAREN
	;

notExpr
	:	equalityExpr
	|	LPAREN NOT op=expr RPAREN
	;

equalityExpr
    :   relationExpr
	|	LPAREN oper=(EQ | NEQ) leftOp=expr rightOp=expr RPAREN
	;

relationExpr
    :   bitwiseOrExpr
	|	LPAREN oper=(LT | LEQ | GT | GEQ | BV_ULT | BV_ULE | BV_UGT | BV_UGE | BV_SLT | BV_SLE | BV_SGT | BV_SGE) leftOp=expr rightOp=expr RPAREN
	;

bitwiseOrExpr
    :   bitwiseXorExpr
    |   LPAREN oper=BV_OR ops+=expr (ops+=expr)* RPAREN
    ;

bitwiseXorExpr
    :   bitwiseAndExpr
    |   LPAREN oper=BV_XOR leftOp=expr rightOp=expr RPAREN
    ;

bitwiseAndExpr
    :   bitwiseShiftExpr
    |   LPAREN oper=BV_AND ops+=expr (ops+=expr)* RPAREN
    ;

bitwiseShiftExpr
    :   additiveExpr
    |   LPAREN oper=(BV_SHL | BV_ASHR | BV_LSHR | BV_ROL | BV_ROR) leftOp=expr rightOp=expr RPAREN
    ;

additiveExpr
    :   multiplicativeExpr
	|	LPAREN oper=(PLUS | MINUS | BV_ADD | BV_SUB | FPADD | FPSUB) ops+=expr (ops+=expr)* RPAREN
	;

multiplicativeExpr
    :   bvConcatExpr
	|	LPAREN oper=(MUL | DIV | MOD | REM | BV_MUL | BV_UDIV | BV_SDIV | BV_SMOD | BV_UREM | BV_SREM | FPREM | FPMUL | FPDIV) ops+=expr (ops+=expr)* RPAREN
	;

bvConcatExpr
    :   bvExtendExpr
    |   LPAREN oper=BV_CONCAT (ops+=expr)+ RPAREN
    ;

bvExtendExpr
    :   unaryExpr
    |   LPAREN oper=(BV_ZERO_EXTEND | BV_SIGN_EXTEND) leftOp=expr rightOp=bvType RPAREN
    ;

unaryExpr
	:	bitwiseNotExpr
	|	LPAREN oper=(PLUS | MINUS | BV_POS | BV_NEG | FP_ABS | FP_IS_INF | FP_IS_NAN | FPROUNDTOINT | FPSQRT | FPTOFP | FPTOBV | FP_FROM_BV | FPNEG | FPPOS ) op=expr RPAREN
	;

bitwiseNotExpr
    :   functionCall
    |   LPAREN BV_NOT op=expr RPAREN
    ;

functionCall
    :   arrayRead
    |   LPAREN FUNC op=expr (ops+=expr)* RPAREN
    ;

arrayRead
    :   arrayWrite
    |   LPAREN READ array=expr index=expr RPAREN
    ;

arrayWrite
    :   primeExpr
    |   LPAREN WRITE array=expr index=expr elem=expr RPAREN
    ;

primeExpr
    :   bvExtract
    |   LPAREN PRIME op=expr RPAREN
    ;

bvExtract
    :   primaryExpr
    |   LPAREN EXTRACT op=expr from=expr until=expr RPAREN
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
    :   LPAREN ARRAY (LPAREN indexExpr+=expr valueExpr+=expr RPAREN)* LPAREN DEFAULT elseExpr=expr RPAREN RPAREN
    |   LPAREN ARRAYINIT (indexExpr+=expr valueExpr+=expr)* elseExpr=expr RPAREN
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
