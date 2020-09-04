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
grammar XtaDsl;

// S P E C I F I C A T I O N

xta	:	(fFunctionDecls+=functionDecl | fVariableDecls+=variableDecl | fTypeDecls+=typeDecl | fProcessDecls+=processDecl)* (fInstantiations+=instantiation)* fSystem=system
	;

iteratorDecl
	:	fId=ID COLON fType=type
	;

instantiation
	:	fId=ID assignOp fProcId=ID LPAREN fArgList=argList RPAREN SEMICOLON
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

processDecl
	:	PROCESS	fId=ID fParameterList=parameterList LBRAC fProcessBody=processBody RBRAC
	;

processBody
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
	:	SELECT fIteratorDecls+=iteratorDecl (COMMA fIteratorDecls+=iteratorDecl)* SEMICOLON
	;

guard
	:	GUARD fExpression=expression SEMICOLON
	;

sync:	SYNC fExpression=expression (fEmit=EXCL | fRecv=QUEST) SEMICOLON
	;

assign
	:	ASSIGN (fExpressions+=expression)(COMMA fExpressions+=expression)* SEMICOLON
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
	:	fId=ID (LBRACK fArrayIndexes+=arrayIndex RBRACK)*
	;

arrayIndex
	:	idIndex
	|	expressionIndex
	;

idIndex
	:	fId=ID
	;

expressionIndex
	:	fExpression=expression
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
	:	FOR LPAREN fIteratorDecl=iteratorDecl RPAREN fStatement=statement
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

expression
	:	quantifiedExpression
	;

quantifiedExpression
	:	textOrImplyExpression
	|	forallExpression
	|	existsExpression
	;

forallExpression
	:	FORALL LPAREN fIteratorDecl=iteratorDecl RPAREN fOp=quantifiedExpression
	;

existsExpression
	:	EXISTS LPAREN fIteratorDecl=iteratorDecl RPAREN fOp=quantifiedExpression
	;

textOrImplyExpression
	:	fOps+=textAndExpression (fOpers+=textOrImplyOp fOps+=textAndExpression)*
	;

textAndExpression
	:	fOps+=textNotExpression (textAndOp fOps+=textNotExpression)*
	;

textNotExpression
	:	assignmentExpression
	|	textNotOp fOp=textNotExpression
	;

assignmentExpression
	:	fLeftOp=conditionalExpression (fOper=assignmentOp fRightOp=assignmentExpression)?
	;

conditionalExpression
	:	fCondOp=logicalOrExpression (QUEST fThenOp=expression COLON fElseOp=conditionalExpression)?
	;

logicalOrExpression
	:	fOps+=logicalAndExpression (logOrOp fOps+=logicalAndExpression)*
	;

logicalAndExpression
	:	fOps+=bitwiseOrExpression (logAndOp fOps+=bitwiseOrExpression)*
	;

bitwiseOrExpression
	:	 fOps+=bitwiseXorExpression (bwOrOp fOps+=bitwiseXorExpression)*
	;

bitwiseXorExpression
	:	fOps+=bitwiseAndExpression (bwXorOp fOps+=bitwiseAndExpression)*
	;

bitwiseAndExpression
	:	fOps+=equalityExpression (bwAndOp fOps+=equalityExpression)*
	;

equalityExpression
	:	fOps+=relationalExpression (fOpers+=equalityOp  fOps+=relationalExpression)*
	;

relationalExpression
	:	fOps+=shiftExpression (fOpers+=relationalOp  fOps+=shiftExpression)*
	;

shiftExpression
	:	fOps+=additiveExpression (fOpers+=shiftOp  fOps+=additiveExpression)*
	;

additiveExpression
	:	fOps+=multiplicativeExpression (fOpers+=additiveOp  fOps+=multiplicativeExpression)*
	;

multiplicativeExpression
	:	fOps+=prefixExpression (fOpers+=multiplicativeOp fOps+=prefixExpression)*
	;

prefixExpression
	:	postfixExpression
	|	fOper=prefixOp fOp=prefixExpression
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
	:	LPAREN fOp=expression RPAREN
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
	:	fAssignOp=assignOp
	|	fAddAssignOp=addAssignOp
	|	fSubAssignOp=subAssignOp
	|	fMulAssignOp=mulAssignOp
	|	fDivAssignOp=divAssignOp
	|	fRemAssignOp=remAssignOp
	|	fBwOrAssignOp=bwOrAssignOp
	|	fBwAndAssignOp=bwAndAssignOp
	|	fBwXorAssignOp=bwXorAssignOp
	|	fShlAssignOp=shlAssignOp
	|	fShrAssignOp=shrAssignOp
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

logOrOp
	:	LOGOROP
	;

logAndOp
	:	LOGANDOP
	;

bwOrOp
	:	BAR
	;

bwXorOp
	:	HAT
	;

bwAndOp
	:	AMP
	;


equalityOp
	:	fEqOp=eqOp
	|	fNeqOp=neqOp
	;

eqOp:	EQOP
	;

neqOp
	:	NEQOP
	;

relationalOp
	:	fLtOp=ltOp
	|	fLeqOp=leqOp
	|	fGtOp=gtOp
	|	fGeqOp=geqOp
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
	:	fAddOp=addOp
	|	fSubOp=subOp
	;

addOp
	:	PLUS
	;

subOp
	:	MINUS
	;

multiplicativeOp
	:	fMulOp=mulOp
	|	fDivOp=divOp
	|	fRemOp=remOp
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
	:	fPreIncOp=preIncOp
	|	fPreDecOp=preDecOp
	|	fPlusOp=plusOp
	|	fMinusOp=minusOp
	|	fLogNotOp=logNotOp
	|	fBwNotOp=bwNotOp
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

logNotOp
	:	EXCL
	;

bwNotOp
	:	TILDE
	;

postfixOp
	:	fPostIncOp=postIncOp
	|	fPostDeclOp=postDecOp
	|	fFuncCallOp=functionCallOp
	|	fArrayAccessOp=arrayAccessOp
	|	fStructSelectOp=structSelectOp
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

LOGOROP
	:	'||'
	;

LOGANDOP
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
