grammar XstsDsl;

xsts:
    typeDeclarations+=typeDeclaration*
    variableDeclarations+=variableDeclaration (variableDeclarations+=variableDeclaration)*
    transitions=tran
    initAction=init
    envAction=env
    PROP LCURLY prop=expr RCURLY;

action:
    assumeAction|
    assignAction|
    havocAction|
    nonDetAction|
    ortAction
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

ortAction:
    ORT LCURLY branches+=sequentialAction RCURLY (LCURLY branches+=sequentialAction RCURLY)*
;

nonDetAction:
    CHOICE nonDet
;

nonDet:
    LCURLY choices+=sequentialAction RCURLY (NONDET_OR LCURLY choices+=sequentialAction RCURLY)*
;

sequentialAction:
    (actions+=action)*;

assumeAction:
    ASSUME cond=expr SEMICOLON;

assignAction:
    lhs=ID ASSIGN rhs=expr SEMICOLON;

havocAction:
    HAVOC name=ID SEMICOLON;

expr:
    iteExpression
;

iteExpression:
    implyExpression |
    IF cond=expr THEN then=expr ELSE elze=expr
;

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
	LPAREN ops+=expr RPAREN | prime
;

prime:
    ref=reference | NEXT LPAREN inner=prime RPAREN;

variableDeclaration:
    CTRL? VAR name=ID DP type=typeName  (EQUALS initValue=value)?;

value:
    literal|reference;

literal:
    INTLIT|BOOLLIT|arrLitExpr
    ;

arrLitExpr
    :   LBRACK (indexExpr+=expr LARROW valueExpr+=expr COMMA)+ (LT indexType=typeName GT)? DEFAULT LARROW elseExpr=expr RBRACK
    |   LBRACK LT indexType=typeName GT DEFAULT LARROW elseExpr=expr RBRACK
    ;

reference:
    name=ID;

typeName:
    INT|BOOL|arrayType|customType;

customType:
    name=ID;

arrayType:
    LBRACK indexType=typeName RBRACK RARROW elemType=typeName;

typeDeclaration:
    TYPE name=ID DP LCURLY literals+=typeLiteral (COMMA literals+=typeLiteral)* RCURLY;

typeLiteral:
    name=ID;

CTRL: 'ctrl';
ORT: 'ort';
IF: 'if';
THEN: 'then';
ELSE: 'else';
TRAN: 'trans';
INIT: 'init';
ENV: 'env';
PROP: 'prop';
HAVOC: 'havoc';
CHOICE: 'choice';
NONDET_OR: 'or';
SEMICOLON: ';';
ASSUME: 'assume';
NEXT: 'next';
AND: '&&';
OR: '||';
IMPLIES: '=>';
LARROW: '<-';
RARROW: '->';
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
LBRACK: '[';
RBRACK: ']';
INTLIT: [0-9]+;
DEFAULT: 'default';
BOOLLIT: 'true' | 'false';
ID: [a-zA-Z_][a-zA-Z0-9_]*;
WS: (' '| '\t' | '\n' | '\r') -> skip;
COMMENT: '/*' .*? '*/' -> skip;
LINE_COMMENT: '//' ~[\r\n]* -> skip;
