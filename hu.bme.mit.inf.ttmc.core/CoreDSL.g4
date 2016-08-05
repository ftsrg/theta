grammar CoreDSL;

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
	
BOOLTYPE
	:	'bool'
	;
	
INTTYPE
	:	'int'
	;
	
RATTYPE
	:	'rat'
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
	:	leftOp=additiveExpr (oper=(LT | LEQ | GT | GEQ) rightOp=additiveExpr)?
	;
	
additiveExpr
	:	ops+=multiplicativeExpr (opers+=(PLUS | MINUS) ops+=multiplicativeExpr)*
	;
	
multiplicativeExpr
	:	ops+=negExpr (opers+=(MUL | RDIV | IDIV | MOD | REM) ops+=negExpr)*
	;
	
negExpr
	:	accessorExpr
	|	MINUS op=negExpr
	;
	
accessorExpr
	:	op=primaryExpr (accesses+=access)*
	;

access
	:	params=funcAccess
	|	indexes=arrayAccess
	;

funcAccess
	:	LPAREN (params=exprList)? RPAREN
	;
	
arrayAccess
	:	LBRACK (indexes=exprList)? RBRACK
	;
	
primaryExpr
	:	trueExpr
	|	falseExpr
	|	intLitExpr
	|	ratLitExpr
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
	
RDIV:	'/'
	;
	
IDIV:	'div'
	;
	
MOD	:	'mod'
	;

REM	:	'rem'
	;
	
PERCENT
	:	'%'
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