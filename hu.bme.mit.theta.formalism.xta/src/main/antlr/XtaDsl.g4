grammar XtaDsl;

// S P E C I F I C A T I O N

xta	:	fDeclarations+=declaration* fInstantiations=instantiation* fSystem=system
	;

declaration
	:	functionDecl
	|	variableDecl
	|	typeDecl
	|	procDecl
	;
	
decl:	tId=ID COLON tType=type
	;
	
instantiation
	:	ID assignOp ID LPAREN fArgList=argList RPAREN SEMICOLON
	;
	
system
	:	SYSTEM fIds+=ID (COMMA fIds+=ID)* SEMICOLON
	;
	
parameterList
	:	LPAREN (fParameterDecls+=parameterDecl (COMMA fParameterDecls+=parameterDecl)*)? RPAREN
	;
	
parameterDecl
	:	fType=type fparameterIds+=parameterId (COMMA fparameterIds+=parameterId)*
	;
	
parameterId
	:	(fRef=AMP)? fArrayId=arrayId
	;

functionDecl
	:	fType=type fId=ID fParameterList=parameterList fBlock=block
	;
	
procDecl
	:	PROCESS	fId=ID fParameterList=parameterList LBRAC fProcBody=procBody RBRAC
	;
	
procBody
	:	(fFunctionDecls+=functionDecl | fVariableDecls+=variableDecl | fTypeDecls+=typeDecl)* fStates=states (fCommit=commit)? (fUrgent=urgent)? fInit=init (fTransitions=transitions)?
	;
	
states
	:	STATE fStateDecls+=stateDecl (COMMA fStateDecls+=stateDecl)* SEMICOLON
	;
	
stateDecl
	:	fId=ID (LBRAC fExpression=expression RBRAC)?
	;
	
commit
	:	COMMIT fStateList=stateList SEMICOLON
	;
	
urgent
	:	URGENT fStateList=stateList SEMICOLON
	;
	
stateList
	:	fIds+=ID (COMMA fIds+=ID)*
	;
	
init:	INIT fId=ID SEMICOLON
	;
	
transitions
	:	TRANS fTransitions+=transition (COMMA fTransitions+=transition)* SEMICOLON
	;
	
transition
	:	fSourceId=ID RARROW fTargetId=ID fTransitionBody=transitionBody
	;
	
transitionOpt
	:	transition
	|	RARROW fTargetId=ID fTransitionBody=transitionBody
	;

transitionBody
	:	LBRAC (fSelect=select)? (fGuard=guard)? (fSync=sync)? (fAssign=assign)? RBRAC
	;
	
select
	:	SELECT fDecls+=decl (COMMA fDecls+=decl)* SEMICOLON
	;
	
guard
	:	GUARD fExpression=expression SEMICOLON
	;
	
sync:	SYNC fExpression=expression (fSend=EXCL | fReceive=QUEST) SEMICOLON
	;
	
assign
	:	ASSIGN fExprList=exprList SEMICOLON
	;
	
SYSTEM
	:	'system'
	;
	
PROCESS
	:	'process'
	;
	
STATE
	:	'state'
	;

COMMIT
	:	'commit'
	;
	
URGENT
	:	'urgent'
	;
	
INIT:	'init'
	;
	
TRANS
	:	'trans'
	;
	
SELECT
	:	'select'
	;
	
GUARD
	:	'guard'
	;
	
SYNC:	'sync'
	;
	
ASSIGN
	:	'assign'
	;

// T Y P E S

typeDecl
	:	TYPEDEF fType=type fArrayIds+=arrayId (COMMA fArrayIds+=arrayId)* SEMICOLON
	;
	
arrayId
	:	fId=ID (fArrayDecls+=arrayDecl)*
	;
	
arrayDecl
	:	LBRACK fExpression=expression RBRACK
	;
	
	
type:	fTypePrefix=typePrefix fBasicType=basicType
	;
	
typePrefix
	:	(fUrgent=URGENT)? (fBroadcast=BROADCAST)? | (fConst=CONST)?
	;	
	
basicType
	:	refType
	|	voidType
	|	intType
	|	clockType
	|	chanType
	|	boolType
	|	rangeType
	|	scalarType
	|	structType
	;
	
refType
	:	fId=ID
	;
	
voidType
	:	VOID
	;
	
intType
	:	INT
	;
	
clockType
	:	CLOCK
	;
	
chanType
	:	CHAN
	;
	
boolType
	:	BOOL
	;
	
rangeType
	:	INT LBRACK fFromExpression=expression COMMA fToExpression=expression RBRACK
	;
	
scalarType
	:	SCALAR LBRACK fExpression=expression RBRACK
	;
	
structType
	:	STRUCT LBRAC (fFieldDecls+=fieldDecl SEMICOLON)+ RBRAC
	;	

fieldDecl
	:	fType=type fArrayIds+=arrayId (COMMA fArrayIds+=arrayId)*
	;
	
TYPEDEF
	:	'typedef'
	;
	
VOID:	'void'
	;
	
INT	:	'int'
	;
	
CLOCK
	:	'clock'
	;
	
CHAN:	'chan'
	;
	
BOOL:	'bool'
	;
	
SCALAR
	:	'scalar'
	;	

STRUCT
	:	'struct'
	;
	
BROADCAST
	:	'broadcast'
	;
	
CONST
	:	'const'
	;
		
// D E C L A R A T I O N S

variableDecl
	:	fType=type fVariableIds+=variableId (COMMA fVariableIds+=variableId)* SEMICOLON
	;
	
variableId
	:	fArrayId=arrayId (assignOp fInitialiser=initialiser)?
	;
	
initialiser
	:	fSimpleInitialiser=simpleInitialiser
	|	fCompundInitialiser=compoundInitialiser
	;
	
simpleInitialiser
	:	fExpression=expression
	;
	
compoundInitialiser
	:	LBRAC fInitialiser=initialiser (COMMA fInitialiser=initialiser)* RBRAC
	;

// S T A T E M E N T S

block
	:	LBRAC (fVariableDecls+=variableDecl | fTypeDecls+=typeDecl)* (fStatements+=statement)* RBRAC
	;

statement
	:	block
	|	skipStatement
	|	expressionStatement
	|	forStatement
	|	foreachStatement
	|	whileStatement
	|	doStatement
	|	ifStatement
	|	returnStatement
	;
	
skipStatement
	:	SEMICOLON
	;
	
expressionStatement
	:	fExpression=expression SEMICOLON
	;
	
forStatement
	:	FOR LPAREN fInitExpression=expression SEMICOLON fConditionExpression=expression SEMICOLON fIncrementExpression=expression RPAREN fStatement=statement
	;
	
foreachStatement
	:	FOR LPAREN fDecl=decl RPAREN fStatement=statement
	;
	
whileStatement
	:	WHILE LPAREN fConditionExpression=expression RPAREN fStatement=statement
	;
	
doStatement
	:	DO fStatement=statement WHILE LPAREN fConditionExpression=expression RPAREN
	;
	
ifStatement
	:	IF LPAREN fConditionExpression=expression RPAREN fThenStatement=statement (ELSE fElseStatement=statement)?
	;

returnStatement
	:	RETURN (fExpression=expression)?
	;

FOR	:	'for'
	;
	
WHILE
	:	'while'
	;

DO	:	'do'
	;
	
IF	:	'if'
	;
	
ELSE:	'else'
	;
	
RETURN
	:	'return'
	;

// E X P R E S S I O N S

////////////////////////////////////////////////////////////////////////////

exprList
	:	(fExpressions+=expression)(COMMA fExpressions+=expression)*
	;

expression
	:	quantifiedExpression
	;
	
quantifiedExpression
	:	textOrImplyExpression
	|	forallExpression
	|	existsExpression
	;
	
forallExpression
	:	FORALL LPAREN fDecl=decl RPAREN fOp+=quantifiedExpression
	;
	
existsExpression
	:	EXISTS LPAREN fDecl=decl RPAREN fOp+=quantifiedExpression
	;
	
textOrImplyExpression
	:	fOps+=textAndExpression (fOper=textOrImplyOp fOps+=textAndExpression)*
	;
	
textAndExpression
	:	fOps+=textNotExpression (textAndOp fOps+=textNotExpression)*
	;
	
textNotExpression
	:	assignmentExpression
	|	textNotOp fOp+=textNotExpression
	;
	
assignmentExpression
	:	fLeftOp=conditionalExpression (fOper=assignmentOp fRightOp=assignmentExpression)?
	;
	
conditionalExpression
	:	fCondOp=logicalOrExpression (QUEST fThenOp=expression COLON fElseOp=conditionalExpression)?
	;
	
logicalOrExpression
	:	fOps+=logicalAndExpression (logicalOrOp fOps+=logicalAndExpression)*
	;
	
logicalAndExpression
	:	fOps+=bitwiseOrExpression (logicalAndOp fOps+=bitwiseOrExpression)*
	;
	
bitwiseOrExpression
	:	 fOps+=bitwiseXorExpression (bitwiseOrOp fOps+=bitwiseXorExpression)*
	;
	
bitwiseXorExpression
	:	fOps+=bitwiseAndExpression (bitwiseXorOp fOps+=bitwiseAndExpression)*
	;
	
bitwiseAndExpression
	:	fOps+=equalityExpression (bitwiseAndOp fOps+=equalityExpression)*
	;
	
	
equalityExpression
	:	fOps+=relationalExpression (fOper=equalityOp  fOps+=relationalExpression)*
	;

relationalExpression
	:	fOps+=shiftExpression (fOper=relationalOp  fOps+=shiftExpression)*
	;
	
shiftExpression
	:	fOps+=additiveExpression (fOper=shiftOp  fOps+=additiveExpression)*
	;
	
additiveExpression
	:	fOps+=multiplicativeExpression (fOper=additiveOp  fOps+=multiplicativeExpression)*
	;
	
multiplicativeExpression
	:	fOps+=prefixExpression (fOper=multiplicativeOp fOps+=prefixExpression)*
	;
	
prefixExpression
	:	postfixExpression
	|	fOper=prefixOp fOp+=prefixExpression
	;
	
postfixExpression
	:	fOp=primaryExpression (fOpers+=postfixOp)*
	;
	
primaryExpression
	:	trueExpression
	|	falseExpression
	|	natExpression
	|	idExpression
	|	parenthesisExpression
	;

trueExpression
	:	TRUE
	;

falseExpression
	:	FALSE
	;
	
natExpression
	:	fValue=NAT
	;
	
idExpression
	:	fId=ID
	;
	
parenthesisExpression
	:	LPAREN fOp+=expression RPAREN
	;

argList
	:	(fExpressions+=expression (COMMA fExpressions+=expression)*)?
	;
	
textOrImplyOp
	:	textOrOp
	|	textImplyOp
	;
	
textOrOp
	:	OR
	;
	
textImplyOp
	:	IMPLY
	;
	
textAndOp
	:	AND
	;
	
textNotOp
	:	NOT
	;
	
assignmentOp
	:	assignOp
	|	addAssignOp
	|	subAssignOp
	|	mulAssignOp
	|	divAssignOp
	|	remAssignOp
	|	bwOrAssignOp
	|	bwAndAssignOp
	|	bwXorAssignOp
	|	shlAssignOp
	|	shrAssignOp
	;

assignOp
	:	OLDASSIGNOP | NEWASSIGNOP
	;
	
addAssignOp
	:	ADDASSIGNOP
	;
	
subAssignOp
	:	SUBASSIGNOP
	;
	
mulAssignOp
	:	MULASSIGNOP
	;

divAssignOp
	:	DIVASSIGNOP
	;
	
remAssignOp
	:	REMASSIGNOP
	;
	
bwOrAssignOp
	:	BWORASSIGNOP
	;
	
bwAndAssignOp
	:	BWANDASSIGNOP
	;

bwXorAssignOp
	:	BWXORASSIGNOP
	;
	
shlAssignOp
	:	SHLASSIGNOP
	;

shrAssignOp
	:	SHRASSIGNOP
	;
	
logicalOrOp
	:	LOROP
	;
	
logicalAndOp
	:	LANDOP
	;
	
bitwiseOrOp
	:	BAR
	;
	
bitwiseXorOp
	:	HAT
	;
	
bitwiseAndOp
	:	AMP
	;

	
equalityOp
	:	eqOp
	|	neqOp
	;
	
eqOp:	EQOP
	;

neqOp
	:	NEQOP
	;
	
relationalOp
	:	ltOp
	|	leqOp
	|	gtOp
	|	geqOp
	;
	
ltOp:	LTOP
	;
	
leqOp
	:	LEQOP
	;
	
gtOp:	GTOP
	;
	
geqOp
	:	GEQOP
	;
	
shiftOp
	:	shlOp
	|	shrOp
	;

shlOp
	:	SHLOP
	;
	
shrOp
	:	SHROP
	;
	
additiveOp
	:	addOp
	|	subOp
	;
	
addOp
	:	PLUS
	;
	
subOp
	:	MINUS
	;
	
multiplicativeOp
	:	mulOp
	|	divOp
	|	remOp
	;
	
mulOp
	:	ASTER
	;
	
divOp
	:	SLASH
	;
	
remOp
	:	PERCENT
	;
	
prefixOp
	:	preIncOp
	|	preDecOp
	|	plusOp
	|	minusOp
	|	lNotOp
	|	bwNotOp
	;

preIncOp
	:	INCOP
	;
	
preDecOp
	:	DECOP
	;
	
plusOp
	:	PLUS
	;
	
minusOp
	:	MINUS
	;
	
lNotOp
	:	EXCL
	;
	
bwNotOp
	:	TILDE
	;
	
postfixOp
	:	postIncOp
	|	postDecOp
	|	functionCallOp
	|	arrayAccessOp
	|	structSelectOp
	;
	
postIncOp
	:	DECOP
	;
	
postDecOp
	:	INCOP
	;

functionCallOp
	:	LPAREN fArgList=argList RPAREN
	;
	
arrayAccessOp
	:	LBRACK fExpression=expression RBRACK
	;
	
structSelectOp
	:	DOT fId=ID
	;
	
FORALL
	:	'forall'
	;
	
EXISTS
	:	'exists'
	;
	
OR	:	'or'
	;
	
IMPLY
	:	'imply'
	;
	
AND	:	'and'
	;
	
NOT	:	'not'
	;
	
LOROP
	:	'||'
	;
	
LANDOP
	:	'&&'
	;
	
SHLOP
	:	'<<'
	;
	
SHROP
	:	'>>'
	;
	
EQOP:	'=='
	;

NEQOP
	:	'!='
	;
	
NEWASSIGNOP
	:	'='
	;
	
OLDASSIGNOP
	:	':='
	;
	
ADDASSIGNOP
	:	'+='
	;
	
SUBASSIGNOP
	:	'-='
	;
	
MULASSIGNOP
	:	'*='
	;
	
DIVASSIGNOP
	:	'/='
	;
	
REMASSIGNOP
	:	'%='
	;
	
BWORASSIGNOP
	:	'|='
	;
	
BWANDASSIGNOP
	:	'&='
	;
	
BWXORASSIGNOP
	:	'^='
	;
	
SHLASSIGNOP
	:	'<<='
	;
	
SHRASSIGNOP
	:	'>>='
	;
	
LTOP:	'<'
	;
	
LEQOP
	:	'<='
	;
	
GTOP:	'>'
	;
	
GEQOP
	:	'>='
	;
	
INCOP
	:	'++'
	;
	
DECOP
	:	'--'
	;
	
TRUE:	'true'
	;
	
FALSE
	:	'false'
	;


// B A S I C   T O K E N S

NAT	:	DIGIT+
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

AMP	:	'&'
	;
	
HAT	:	'^'
	;
	
BAR	:	'|'
	;
	
EXCL:	'!'
	;
	
QUEST
	:	'?'
	;
	
PERCENT
	:	'%'
	;
	
PLUS:	'+'
	;
	
MINUS
	:	'-'
	;
	
ASTER
	:	'*'
	;
	
SLASH
	:	'/'
	;
	
TILDE
	:	'~'
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