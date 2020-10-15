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

expr: LPAREN expr RPAREN                            # nop
    | simpleExpr                                    # simple
    | (namedExpr | LPAREN namedExpr (COMMA namedExpr) RPAREN) LPAREN expr RARROW expr RPAREN      # nextEdge
    | (namedExpr | LPAREN namedExpr (COMMA namedExpr) RPAREN) LPAREN expr RLONGARROW expr RPAREN  # successorEdges
    | FOREACHVAR BEGIN expr END                     # forEachVar
    | FOREACHTHREAD BEGIN expr END                  # forEachThread
    | FOREACHNODE expr BEGIN expr END               # forEach
    | expr UNION expr                               # unionExpr
    | expr SECTION expr                             # sectionExpr
    | expr SETMINUS expr                            # setMinusExpr
    | expr ASTERISK expr                            # multiplyExpr
    | SOURCE LPAREN expr RPAREN                     # sourceExpr
    | TARGET LPAREN expr RPAREN                     # targetExpr
    ;

simpleExpr
    : EMPTYSET
    | namedExpr
    | taggedExpr
    ;

namedExpr
    : (name=ID)
    ;
    
taggedExpr
    : namedExpr (LBRACK tags+=ID RBRACK)+
    ;

constraints
    : simpleConstraint*
    ;
//
//constraint
//    : LPAREN constraint RPAREN      # nopConstraint
//    | simpleConstraint              # simpleConstr
//    | constraint AND constraint     # andConstraint
//    | constraint OR constraint      # orConstraint
//    | NOT constraint                # notConstraint
//    | constraint RARROW constraint  # implyConstraint
//    ;

simpleConstraint
    : (NOT)? (name=ID) (ACYCLIC | EMPTY)
    ;


// B A S I C   T O K E N S

FOREACHVAR
    :   'for_each_var'
    ;

FOREACHTHREAD
    :   'for_each_thread'
    ;

FOREACHNODE
    :   'for_each_node'
    ;

SOURCE
    :   'source'
    ;

TARGET
    :   'target'
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