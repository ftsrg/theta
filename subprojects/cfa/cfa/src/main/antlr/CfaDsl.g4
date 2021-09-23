/*
 *  Copyright 2017 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
grammar CfaDsl;

// S P E C I F I C A T I O N

spec:	(varDecls+=varDecl | procDecls+=procDecl)*
	;

varDecl
	:	VAR ddecl=decl
	;

procDecl
	:	(main=MAIN)? PROCESS id=ID (LPAREN (paramDecls=declList)? RPAREN)? LBRAC
			(varDecls+=varDecl | locs+=loc | edges+=edge)*
		RBRAC
	;

loc	:	(init=INIT | finall=FINAL | error=ERROR)? LOC id=ID
	;

edge:	source=ID RARROW target=ID (LBRAC
			(stmts+=stmt)*
		RBRAC)?
	;

VAR	:	'var'
	;

MAIN:	'main'
	;

PROCESS
	:	'process'
	;

INIT:	'init'
	;

FINAL
	:	'final'
	;

ERROR
	:	'error'
	;

LOC	:	'loc'
	;


// D E C L A R A T I O N S

decl:	name=ID COLON ttype=type
	;

declList
	:	(decls+=decl)(COMMA decls+=decl)*
	;


// T Y P E S

type:	boolType
	|	intType
	|	ratType
	|	funcType
	|	arrayType
	|	bvType
	|   fpType
	;

typeList
	:	(types+=type)(COMMA types+=type)*
	;

boolType
	:	BOOLTYPE
	;

intType
	:	INTTYPE
	;

ratType
	:	RATTYPE
	;

funcType
	:	LPAREN paramTypes=typeList RPAREN RARROW returnType=type
	;

arrayType
	:	LBRACK indexType=type RBRACK RARROW elemType=type
	;

bvType
    :   BVTYPE LBRACK size=INT RBRACK
    ;

fpType
    :   FPTYPE FP_TYPE_DECL
    ;

BOOLTYPE
	:	'bool'
	;

INTTYPE
	:	'int'
	;

RATTYPE
	:	'rat'
	;

BVTYPE
    :   'bv'
    ;

FPTYPE
    :   'fp'
    ;

// E X P R E S S I O N S

expr:	funcLitExpr
	;

exprList
	:	(exprs+=expr)(COMMA exprs+=expr)*
	;

funcLitExpr
	:	iteExpr
	|	LPAREN (paramDecls=declList)? RPAREN RARROW result=funcLitExpr
	;

iteExpr
	:	iffExpr
	|	IF cond=expr THEN then=expr ELSE elze=iteExpr
	;

iffExpr
	:	leftOp=implyExpr (IFF rightOp=iffExpr)?
	;

implyExpr
	:	leftOp=quantifiedExpr (IMPLY rightOp=implyExpr)?
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

////

IF	:	'if'
	;

THEN:	'then'
	;

ELSE:	'else'
	;

IFF	:	'iff'
	;

IMPLY
	:	'imply'
	;

FORALL
	:	'forall'
	;

EXISTS
	:	'exists'
	;

OR	:	'or'
	;

AND	:	'and'
	;

XOR	:	'xor'
	;

NOT	:	'not'
	;

EQ	:	'='
	;

NEQ	:	'/='
	;

LT	:	'<'
	;

LEQ	:	'<='
	;

GT	:	'>'
	;

GEQ	:	'>='
	;

PLUS:	'+'
	;

MINUS
	:	'-'
	;

MUL	:	'*'
	;

DIV	:	'/'
	;

MOD	:	'mod'
	;

REM	:	'rem'
	;

PERCENT
	:	'%'
	;

BV_CONCAT
    :   PLUS PLUS
    ;

BV_ZERO_EXTEND
    :   'bv_zero_extend'
    ;

BV_SIGN_EXTEND
    :   'bv_sign_extend'
    ;

BV_ADD
    :   'bvadd'
    ;

BV_SUB
    :   'bvsub'
    ;

BV_POS
    :   'bvpos'
    ;

BV_NEG
    :   'bvneg'
    ;

BV_MUL
    :   'bvmul'
    ;

BV_UDIV
    :   'bvudiv'
    ;

BV_SDIV
    :   'bvsdiv'
    ;

BV_SMOD
    :   'bvsmod'
    ;

BV_UREM
    :   'bvurem'
    ;

BV_SREM
    :   'bvsrem'
    ;

BV_OR
    :   'bvor'
    ;

BV_AND
    :   'bvand'
    ;

BV_XOR
    :   'bvxor'
    ;

BV_NOT
    :   'bvnot'
    ;

BV_SHL
    :   'bvshl'
    ;

BV_ASHR
    :   'bvashr'
    ;

BV_LSHR
    :   'bvlshr'
    ;

BV_ROL
    :   'bvrol'
    ;

BV_ROR
    :   'bvror'
    ;

BV_ULT
    :   'bvult'
    ;

BV_ULE
    :   'bvule'
    ;

BV_UGT
    :   'bvugt'
    ;

BV_UGE
    :   'bvuge'
    ;

BV_SLT
    :   'bvslt'
    ;

BV_SLE
    :   'bvsle'
    ;

BV_SGT
    :   'bvsgt'
    ;

BV_SGE
    :   'bvsge'
    ;

FP_ABS
    :   'fpabs'
    ;

FP_FROM_BV
    :   'fpfrombv' FP_TYPE_DECL (LBRACK SIGNEDNESS RBRACK) FP_ROUNDINGMODE?
    ;

FP_IS_NAN
    :   'fpisnan'
    ;

FPMAX
    :   'fpmax'
    ;

FPMIN
    :   'fpmin'
    ;

FPREM
    :   'fprem'
    ;

FPROUNDTOINT
    :   'fproundtoint' FP_ROUNDINGMODE?
    ;

FPSQRT
    :   'fpsqrt' FP_ROUNDINGMODE?
    ;

FPTOBV
    :   'fptobv' BV_TYPE_DECL FP_ROUNDINGMODE?
    ;

FPTOFP
    :   'fptofp' FP_TYPE_DECL FP_ROUNDINGMODE?
    ;

FPSUB
    :   'fpsub' FP_ROUNDINGMODE?
    ;

FPADD
    :   'fpadd' FP_ROUNDINGMODE?
    ;

FPMUL
    :   'fpmul' FP_ROUNDINGMODE?
    ;

FPDIV
    :   'fpdiv' FP_ROUNDINGMODE?
    ;

FPPOS
    :   'fppos' FP_ROUNDINGMODE?
    ;

FPNEG
    :   'fpneg' FP_ROUNDINGMODE?
    ;

TRUE:	'true'
	;

BV_TYPE_DECL
    :   LBRACK NAT '\'' SIGNEDNESS RBRACK
    ;

SIGNEDNESS
    :   ('u' | 's')
    ;

FP_TYPE_DECL
    :   LBRACK NAT COLON NAT RBRACK
    ;

FP_ROUNDINGMODE
    :   LBRACK [A-Z]* RBRACK
    ;

FALSE
	:	'false'
	;

DEFAULT
    :   'default'
    ;

// S T A T E M E N T S

stmt:	assignStmt
	|	havocStmt
	|	assumeStmt
	|	returnStmt
	;

stmtList
	:	(stmts+=stmt)(SEMICOLON stmts+=stmt)
	;

assignStmt
	:	lhs=ID ASSIGN value=expr
	;

havocStmt
	:	HAVOC lhs=ID
	;

assumeStmt
	:	ASSUME cond=expr
	;

returnStmt
	:	RETURN value=expr
	;

//

ASSIGN
	:	':='
	;

HAVOC
	:	'havoc'
	;

ASSUME
	:	'assume'
	;

RETURN
	:	'return'
	;

// B A S I C   T O K E N S

BV  :   NAT '\'b' [0-1]+
    |   NAT '\'d' (PLUS | MINUS)? INT
    |   NAT '\'x' [0-9a-fA-F]+
    ;

INT	:	NAT
	;

NAT	:	DIGIT+
	;

SIGN:	PLUS | MINUS
	;

DOT	:	'.'
	;

ID	:	(LETTER | UNDERSCORE) (LETTER | UNDERSCORE | DIGIT)*
	;

UNDERSCORE
	:	'_'
	;

DIGIT
	:	[0-9]
	;

LETTER
	:	[a-zA-Z]
	;

LPAREN
	:	'('
	;

RPAREN
	:	')'
	;

LBRACK
	:	'['
	;

RBRACK
	:	']'
	;

LBRAC
	:	'{'
	;

RBRAC
	:	'}'
	;

COMMA
	:	','
	;

COLON
	:	':'
	;

SEMICOLON
	:	';'
	;

QUOT:	'\''
	;

LARROW
	:	'<-'
	;

RARROW
	:	'->'
	;

// Whitespace and comments

WS  :  [ \t\r\n\u000C]+ -> skip
    ;

COMMENT
    :   '/*' .*? '*/' -> skip
    ;

LINE_COMMENT
    :   '//' ~[\r\n]* -> skip
    ;
 
