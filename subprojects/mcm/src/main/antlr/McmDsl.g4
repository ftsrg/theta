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
grammar McmDsl;


specification
    : definitions constraints
    ;

definitions
    : (definition)*
    ;

definition
    : (name=ID) EQ expr
    ;

expr: LPAREN expr RPAREN
    | simpleExpr
    | namedExpr LPAREN expr RARROW expr RPAREN
    | namedExpr LPAREN expr RLONGARROW expr RPAREN
    | FOREACHVAR BEGIN expr END
    | FOREACHTHREAD BEGIN expr END
    | FOREACH expr BEGIN expr END
    | expr UNION expr
    | expr SECTION expr
    | expr SETMINUS expr
    | expr ASTERISK expr
    | expr RARROW expr
    | expr RLONGARROW expr
    ;

simpleExpr
    : EMPTYSET
    | namedExpr
    | patternExpr
    | taggedExpr
    ;

namedExpr
    : (name=ID)
    ;

patternExpr
    : ASTERISK ((name=ID) (LBRACK tag=ID RBRACK)?)?
    ;
    
taggedExpr
    : (name=ID) (LBRACK tags+=ID RBRACK)+
    ;

constraints
    : constraint*
    ;

constraint
    : (name=ID)
    | LPAREN constraint RPAREN
    | simpleConstraint
    | constraint AND constraint
    | constraint OR constraint
    | NOT constraint
    | constraint RARROW constraint
    ;

simpleConstraint
    : (name=ID) NOT? (ACYCLIC | IRREFLEXIVE | EMPTY)
    ;


// B A S I C   T O K E N S

FOREACHVAR
    :   'for_each_var'
    ;

FOREACHTHREAD
    :   'for_each_thread'
    ;

FOREACH
    :   'for_each'
    ;

BEGIN
    :   'begin'
    ;

END :   'end'
    ;

UNION
    :   'union'
    ;

SECTION
    :   'intersect'
    ;

SETMINUS
    :   '\\'
    ;

ASTERISK
    :   '*'
    ;


AND :   'and'
    ;

OR  :   'or'
    ;

EMPTYSET
    :   '{}'
    ;

EMPTY
    :   'empty'
    ;

IRREFLEXIVE
    :   'irreflexive'
    ;

ACYCLIC
    :   'acyclic'
    ;

NOT :   'not'
    ;

EQ  :   '='
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

RLONGARROW
	:	'-->'
	;

ATSIGN
	:	'@'
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