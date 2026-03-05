/*
 *  Copyright 2025 Budapest University of Technology and Economics
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

grammar dve;

// ============================================================================
// Parser rules
// ============================================================================

model
    : topDecl* processDecl+ systemDecl EOF
    ;

topDecl
    : varDecl SEMI
    | arrayDecl SEMI
    | channelDecl SEMI
    ;

// ---- Variable declarations -------------------------------------------------

varDecl
    : varType ID (ASSIGN expr)?
    ;

arrayDecl
    : varType ID LBRACKET INT_LITERAL RBRACKET (ASSIGN LBRACE exprList RBRACE)?
    ;

varType
    : BYTE
    | INT
    ;

// ---- Channel declarations --------------------------------------------------

// channel name {0};                    — synchronous, no data
// channel name {byte, int} [cap];      — typed fields, capacity >= 0
channelDecl
    : CHANNEL ID LBRACE INT_LITERAL RBRACE                                       # syncNoDataChannel
    | CHANNEL ID LBRACE varTypeList RBRACE LBRACKET INT_LITERAL RBRACKET         # typedChannel
    ;

varTypeList
    : varType (COMMA varType)*
    ;

// ---- Process declarations --------------------------------------------------

processDecl
    : PROCESS ID LBRACE processBody RBRACE
    ;

// Order: local vars*, state, init, (accept | commit)*, assert?, trans?
processBody
    : localDecl* stateDecl initDecl (acceptDecl | commitDecl)* assertDecl? transPart
    ;

localDecl
    : varDecl SEMI
    | arrayDecl SEMI
    ;

stateDecl
    : STATE idList SEMI
    ;

initDecl
    : INIT ID SEMI
    ;

acceptDecl
    : ACCEPT idList SEMI
    ;

commitDecl
    : COMMIT idList SEMI
    ;

assertDecl
    : ASSERT assertItem (COMMA assertItem)* SEMI
    ;

assertItem
    : ID COLON expr
    ;

// Transitions are comma-separated, terminated by semicolon; may be absent
transPart
    : TRANS transition (COMMA transition)* SEMI
    |
    ;

transition
    : ID ARROW ID LBRACE transClause* RBRACE
    ;

// All clauses are optional and can appear in any order
transClause
    : GUARD expr SEMI        # guardClause
    | SYNC syncAction SEMI   # syncClause
    | EFFECT effectList SEMI # effectClause
    ;

// sync ch!expr, expr  — send values
// sync ch?lval, lval  — receive into lvalues
// data list is optional for no-data channels
syncAction
    : ID BANG  (expr  (COMMA expr )*)?  # syncSend
    | ID QUEST (lvalue (COMMA lvalue)*)? # syncRecv
    ;

effectList
    : assignment (COMMA assignment)*
    ;

assignment
    : lvalue ASSIGN expr
    ;

// ---- LValues ---------------------------------------------------------------

lvalue
    : ID                                        # simpleLValue
    | ID LBRACKET expr RBRACKET                 # arrayLValue
    | ID DOT ID                                 # qualLValue
    | ID DOT ID LBRACKET expr RBRACKET          # qualArrayLValue
    ;

// ---- System declaration ----------------------------------------------------

systemDecl
    : SYSTEM systemType (PROPERTY ID)? SEMI
    ;

systemType
    : ASYNC
    | SYNC
    ;

// ---- Expressions -----------------------------------------------------------
// Listed lowest-to-highest precedence (ANTLR4 resolves left-recursive rules
// by treating earlier alternatives as having lower precedence).

expr
    : expr OR   expr                             # logOrExpr
    | expr AND  expr                             # logAndExpr
    | expr BITOR  expr                           # bitOrExpr
    | expr BITXOR expr                           # bitXorExpr
    | expr BITAND expr                           # bitAndExpr
    | expr (EQ2 | NEQ) expr                      # eqExpr
    | expr (LT | LEQ | GT | GEQ) expr            # relExpr
    | expr (SHL | SHR) expr                      # shiftExpr
    | expr (PLUS | MINUS) expr                   # addExpr
    | expr (STAR | DIV | MOD) expr               # mulExpr
    | (BANG | MINUS | BITNOT) expr               # unaryExpr
    | atom                                       # atomExpr
    ;

// Atoms: literals, references, qualified accesses, parentheses.
// ID.ID is syntactically ambiguous (var ref vs process state test);
// resolution is deferred to a post-parse semantic pass.
atom
    : INT_LITERAL                                 # intLit
    | ID                                          # simpleRef
    | ID LBRACKET expr RBRACKET                   # arrayRef
    | ID DOT ID                                   # qualifiedRef
    | ID DOT ID LBRACKET expr RBRACKET            # qualifiedArrayRef
    | LPAREN expr RPAREN                          # parenExpr
    ;

// ---- Helpers ---------------------------------------------------------------

idList
    : ID (COMMA ID)*
    ;

exprList
    : expr (COMMA expr)*
    ;

// ============================================================================
// Lexer rules — keywords must appear before ID
// ============================================================================

BYTE     : 'byte'     ;
INT      : 'int'      ;
PROCESS  : 'process'  ;
STATE    : 'state'    ;
INIT     : 'init'     ;
ACCEPT   : 'accept'   ;
COMMIT   : 'commit'   ;
ASSERT   : 'assert'   ;
TRANS    : 'trans'    ;
GUARD    : 'guard'    ;
SYNC     : 'sync'     ;
EFFECT   : 'effect'   ;
CHANNEL  : 'channel'  ;
SYSTEM   : 'system'   ;
ASYNC    : 'async'    ;
PROPERTY : 'property' ;

ID          : [a-zA-Z_][a-zA-Z0-9_]* ;
INT_LITERAL : [0-9]+                  ;

ARROW       : '->'  ;
ASSIGN      : '='   ;
EQ2         : '=='  ;
NEQ         : '!='  ;
LEQ         : '<='  ;
GEQ         : '>='  ;
SHL         : '<<'  ;
SHR         : '>>'  ;
AND         : '&&'  ;
OR          : '||'  ;

LT          : '<'   ;
GT          : '>'   ;
PLUS        : '+'   ;
MINUS       : '-'   ;
STAR        : '*'   ;
DIV         : '/'   ;
MOD         : '%'   ;
BANG        : '!'   ;
BITNOT      : '~'   ;
BITAND      : '&'   ;
BITOR       : '|'   ;
BITXOR      : '^'   ;
QUEST       : '?'   ;

LPAREN      : '('   ;
RPAREN      : ')'   ;
LBRACKET    : '['   ;
RBRACKET    : ']'   ;
LBRACE      : '{'   ;
RBRACE      : '}'   ;
SEMI        : ';'   ;
COMMA       : ','   ;
COLON       : ':'   ;
DOT         : '.'   ;

WS            : [ \t\r\n]+    -> skip ;
LINE_COMMENT  : '//' ~[\r\n]* -> skip ;
BLOCK_COMMENT : '/*' .*? '*/' -> skip ;
