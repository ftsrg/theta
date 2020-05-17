grammar XstsDsl;

xsts:
    typeDeclarations+=typeDeclaration*
    variableDeclarations+=variableDeclaration (variableDeclarations+=variableDeclaration)*
    transitions=tran
    initAction=init
    envAction=env
    PROP LCURLY prop=implyExpression RCURLY;

action:
    assumeAction|
    assignAction|
    havocAction|
    nonDetAction
    ;

tran:
    TRAN nonDet
;

env:
    ENV nonDet
;

init:
    INIT nonDet
;

nonDetAction:
    CHOICE nonDet
;

nonDet:
    LCURLY choices+=sequentialAction RCURLY (NONDET_OR LCURLY choices+=sequentialAction RCURLY)*
;

sequentialAction:
    actions+=action (actions+=action)*;

assumeAction:
    ASSUME cond=implyExpression SEMICOLON;

assignAction:
    lhs=prime ASSIGN rhs=implyExpression SEMICOLON;

havocAction:
    HAVOC name=ID SEMICOLON;

implyExpression:
	ops+=orExpr (IMPLIES ops+=orExpr)?
;

orExpr:
	ops+=andExpr (OR ops+=andExpr)*
;

andExpr:
	ops+=notExpr (AND ops+=notExpr)*
;

notExpr:
	eqExpr|
	NOT ops+=notExpr
;

eqExpr:
	ops+=relationExpr (oper=eqOperator ops+=relationExpr)?
;

eqOperator:
	EQ|NEQ
;

relationExpr:
	ops+=additiveExpr (oper=relationOperator ops+=additiveExpr)?
;

relationOperator:
	LT|GT|LEQ|GEQ
;

additiveExpr:
	ops+=multiplicativeExpr (opers+=additiveOperator ops+=multiplicativeExpr)*
;

additiveOperator:
	PLUS|MINUS
;

multiplicativeExpr:
	ops+=negExpr (opers+=multiplicativeOperator ops+=negExpr)*
;

multiplicativeOperator:
	MUL|DIV|MOD
;

negExpr:
	primaryExpr|
	MINUS ops+=negExpr
;

primaryExpr:
	value|
	parenExpr
;

parenExpr:
	LPAREN ops+=implyExpression RPAREN | prime
;

prime:
    ref=reference | NEXT LPAREN inner=prime RPAREN;

variableDeclaration:
    VAR name=ID DP type=typeName (EQUALS initValue=value)?;

value:
    literal|reference;

literal:
    INTLIT|BOOLLIT
    ;

reference:
    name=ID;

typeName:
    INT|BOOL|customType;

customType:
    name=ID;

typeDeclaration:
    TYPE name=ID DP LCURLY literals+=typeLiteral (COMMA literals+=typeLiteral)* RCURLY;

typeLiteral:
    name=ID;

TRAN: 'trans';
INIT: 'init';
ENV: 'env';
PROP: 'prop';
LBRAC: '[';
RBRAC: ']';
HAVOC: 'havoc';
CHOICE: 'choice';
NONDET_OR: 'or';
SEMICOLON: ';';
ASSUME: 'assume';
NEXT: 'next';
AND: '&&';
OR: '||';
IMPLIES: '->';
NOT: '!';
EQ: '==';
NEQ: '!=';
LT: '<';
GT: '>';
LEQ: '<=';
GEQ: '>=';
PLUS: '+';
MINUS: '-';
MUL: '*';
DIV: '/';
MOD: '%';
LPAREN: '(';
RPAREN: ')';
PRIME: '\'';
ASSIGN: ':=';
EQUALS: '=';
VAR: 'var';
INT: 'integer';
BOOL: 'boolean';
DP: ':';
COMMA: ',';
TYPE: 'type';
LCURLY: '{';
RCURLY: '}';
INTLIT: [0-9]+;
BOOLLIT: 'true' | 'false';
ID: [a-zA-Z_][a-zA-Z0-9_]*;
WS: (' '| '\t' | '\n' | '\r') -> skip;