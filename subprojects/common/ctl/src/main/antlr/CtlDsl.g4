/*
 *  Copyright 2026 Budapest University of Technology and Economics
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
grammar CtlDsl;

// Precedence, loosest to tightest: <-> , -> , | , & , unary (! EX EG EF AX AG AF),
// E[_ U _] / A[_ U _], then atoms / parentheses. An atom is a relational expression over
// arithmetic (as in the LTL grammar), so `x >= 0 & x <= 9` is And(Atom(x>=0), Atom(x<=9)).

model : iffExpr EOF ;

iffExpr : ops+=implyExpr (IFF ops+=implyExpr)* ;

implyExpr : ops+=orExpr (IMPLY ops+=orExpr)* ;

orExpr : ops+=andExpr (OR ops+=andExpr)* ;

andExpr : ops+=unaryExpr (AND ops+=unaryExpr)* ;

unaryExpr
    : NOT op=unaryExpr   # NotExpr
    | EX op=unaryExpr    # ExExpr
    | EF op=unaryExpr    # EfExpr
    | EG op=unaryExpr    # EgExpr
    | AX op=unaryExpr    # AxExpr
    | AF op=unaryExpr    # AfExpr
    | AG op=unaryExpr    # AgExpr
    | quantExpr          # QuantPassthrough
    ;

quantExpr
    : E LBRACK l=iffExpr UNTIL r=iffExpr RBRACK   # EuExpr
    | A LBRACK l=iffExpr UNTIL r=iffExpr RBRACK   # AuExpr
    | LPAREN iffExpr RPAREN                       # ParenCtlExpr
    | atom                                        # AtomExpr
    ;

atom : relationExpr ;

relationExpr : ops+=additiveExpr (oper=relationOp ops+=additiveExpr)? ;

relationOp : EQ | NEQ | LT | GT | LEQ | GEQ ;

additiveExpr : ops+=multiplicativeExpr (opers+=additiveOp ops+=multiplicativeExpr)* ;

additiveOp : PLUS | MINUS ;

multiplicativeExpr : ops+=primaryArith (opers+=multiplicativeOp ops+=primaryArith)* ;

multiplicativeOp : MUL | DIV | MOD ;

primaryArith
    : value=INTLIT                # IntLitExpr
    | value=BOOLLIT               # BoolLitExpr
    | name=ID                     # VarExpr
    | MINUS op=primaryArith       # NegArithExpr
    | LPAREN additiveExpr RPAREN  # ParenArithExpr
    ;

// Keywords are declared before ID but win only on an exact match (`EXtra` is an identifier);
// a variable named literally EX/EF/EG/AX/AF/AG/E/A/U clashes with a keyword.

EX     : 'EX' ;
EF     : 'EF' ;
EG     : 'EG' ;
AX     : 'AX' ;
AF     : 'AF' ;
AG     : 'AG' ;
E      : 'E' ;
A      : 'A' ;
UNTIL  : 'U' ;

IFF    : '<->' | '<=>' ;
IMPLY  : '->' | '=>' ;
NOT    : '!' | 'not' | 'NOT' ;
AND    : '&' | '&&' | 'and' | 'AND' ;
OR     : '|' | '||' | 'or' | 'OR' ;

NEQ    : '!=' | '/=' ;
EQ     : '=' | '==' ;
LEQ    : '<=' ;
GEQ    : '>=' ;
LT     : '<' ;
GT     : '>' ;

PLUS   : '+' ;
MINUS  : '-' ;
MUL    : '*' ;
DIV    : '/' ;
MOD    : '%' ;

LPAREN : '(' ;
RPAREN : ')' ;
LBRACK : '[' ;
RBRACK : ']' ;

BOOLLIT : 'true' | 'false' ;
INTLIT  : [0-9]+ ;
ID      : [a-zA-Z_][a-zA-Z0-9_]* ;

WS     : [ \t\r\n]+ -> skip ;
