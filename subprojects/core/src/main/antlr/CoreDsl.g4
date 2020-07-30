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
grammar CoreDsl;

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
	|   bvType
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
	:	LBRACK indexTypes=typeList RBRACK RARROW elemType=type
	;

bvType
    :   ubvType
    |   sbvType
    ;

ubvType
    :   UBVTYPE LBRACK size=INT RBRACK
    ;

sbvType
    :   SBVTYPE LBRACK size=INT RBRACK
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

UBVTYPE
    :   'bv'
    |   'bitvec'
    |   'ubv'
    |   'ubitvec'
    ;

SBVTYPE
    :   'sbv'
    |   'sbitvec'
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
	:	orExpr
	|	forallExpr
	|	existsExpr
	;

forallExpr
	:	FORALL LPAREN paramDecls=declList RPAREN op=quantifiedExpr
	;

existsExpr
	:	EXISTS LPAREN paramDecls=declList RPAREN op=quantifiedExpr
	;

orExpr
	:	ops+=andExpr (OR ops+=andExpr)*
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
	:	leftOp=bitwiseOrExpr (oper=(LT | LEQ | GT | GEQ) rightOp=bitwiseOrExpr)?
	;

bitwiseOrExpr
    :   leftOp=bitwiseXorExpr (oper=BITWISE_OR rightOp=bitwiseXorExpr)?
    ;

bitwiseXorExpr
    :   leftOp=bitwiseAndExpr (oper=BITWISE_XOR rightOp=bitwiseAndExpr)?
    ;

bitwiseAndExpr
    :   leftOp=bitwiseShiftExpr (oper=BITWISE_AND rightOp=bitwiseShiftExpr)?
    ;

bitwiseShiftExpr
    :   leftOp=additiveExpr (oper=(BITWISE_SHIFT_LEFT | BITWISE_ARITH_SHIFT_RIGHT | BITWISE_LOGIC_SHIFT_RIGHT | BITWISE_ROTATE_LEFT | BITWISE_ROTATE_RIGHT) rightOp=additiveExpr)?
    ;

additiveExpr
	:	ops+=multiplicativeExpr (opers+=(PLUS | MINUS) ops+=multiplicativeExpr)*
	;

multiplicativeExpr
	:	ops+=negExpr (opers+=(MUL | DIV | MOD | REM) ops+=negExpr)*
	;

negExpr
	:	bitwiseNotExpr
	|	MINUS op=negExpr
	;

bitwiseNotExpr
    :   accessorExpr
    |   BITWISE_NOT op=bitwiseNotExpr
    ;

accessorExpr
	:	op=primaryExpr (accesses+=access)*
	;

access
	:	params=funcAccess
	|	indexes=arrayAccess
	|	prime=primeAccess
	;

funcAccess
	:	LPAREN (params=exprList)? RPAREN
	;

arrayAccess
	:	LBRACK (indexes=exprList)? RBRACK
	;

primeAccess
	:	QUOT
	;

primaryExpr
	:	trueExpr
	|	falseExpr
	|	intLitExpr
	|	ratLitExpr
	|   bvLitExpr
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

bvLitExpr
    :   bv=BV
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

BITWISE_OR
    :   '|'
    ;

BITWISE_XOR
    :   '^'
    ;

BITWISE_AND
    :   '&'
    ;

BITWISE_SHIFT_LEFT
    :   LT LT
    ;

BITWISE_ARITH_SHIFT_RIGHT
    :   GT GT
    ;

BITWISE_LOGIC_SHIFT_RIGHT
   :   GT GT GT
   ;

BITWISE_ROTATE_LEFT
    :   LT LT BITWISE_NOT
    ;

BITWISE_ROTATE_RIGHT
    :   BITWISE_NOT GT GT
    ;

BITWISE_NOT
    :   '~'
    ;

TRUE:	'true'
	;
	
FALSE
	:	'false'
	;

// S T A T E M E N T S

stmt:	assignStmt
	|	havocStmt
	|	assumeStmt
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

// B A S I C   T O K E N S

BV  :   NAT '\'b' ('s'|'u')? [0-1]+
    |   NAT '\'d' ('s'|'u')? INT
    |   NAT '\'x' ('s'|'u')? [0-9a-fA-F]+
    ;

INT	:	SIGN? NAT
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
