grammar Cat;

mcm
    :   name? scopeBody EOF
    ;

name:   (QUOT? NAME+ QUOT?)
    ;

scopeBody
    :   (procCall | functionDef | procDef | definition | includeFile)*
    ;

procCall
    :   CALL proc = NAME LPAR params += expression (COMMA params += expression)* RPAR
    ;

functionDef
    :   LET n = NAME LPAR params+=NAME (COMMA params+=NAME)* RPAR EQ e = expression
    |   LET n = NAME (params+=NAME)+ EQ e = expression
    ;

procDef
    :   PROCEDURE n = NAME LPAR params+=NAME (COMMA params+=NAME)* RPAR EQ body=scopeBody END
    ;

includeFile
    :   INCLUDE QUOT file = NAME QUOT
    ;

definition
    :   axiomDefinition
    |   letDefinition
    ;

axiomDefinition
    :   (negate = NOT)? ACYCLIC e = expression (AS NAME)?               # acyclicDefinition
    |   (negate = NOT)? IRREFLEXIVE e = expression (AS NAME)?           # irreflexiveDefinition
    |   (negate = NOT)? EMPTY e = expression (AS NAME)?                 # emptyDefinition
    ;

letDefinition
    :   LET REC? n = NAME EQ e = expression letAndDefinition*
    ;

letAndDefinition
    :   AND n = NAME EQ e = expression
    ;

expression
    :   e1 = expression STAR e2 = expression                            # exprCartesian
    |   e = expression (POW)? STAR                                      # exprTransRef
    |   e = expression (POW)? PLUS                                      # exprTransitive
    |   e = expression (POW)? INV                                       # exprInverse
    |   e = expression OPT                                              # exprOptional
    |   NOT e = expression                                              # exprComplement
    |   e1 = expression SEMI e2 = expression                            # exprComposition
    |   e1 = expression BAR e2 = expression                             # exprUnion
    |   e1 = expression BSLASH e2 = expression                          # exprMinus
    |   e1 = expression AMP e2 = expression                             # exprIntersection
    |   fun = NAME LPAR e += expression (COMMA e += expression)* RPAR   # exprFunctionCall
    |   DOMAIN e = expression                                           # exprDomain
    |   RANGE e = expression                                            # exprRange
    |   LPAR e = expression RPAR                                        # expr
    |   n = NAME                                                        # exprBasic
    |   TRY e = expression WITH ('0' | expression)                      # exprTryWith
    |   ('0' | '{' '}')                                                 # exprNull
    |   LBRAC e = expression RBRAC                                      # exprToid
    ;

LET     :   'let';
REC     :   'rec';
AND     :   'and';
AS      :   'as';
TRY     :   'try';
WITH    :   'with';
CALL    :   'call';
PROCEDURE:  'procedure';
END     :   'end';
INCLUDE :   'include';

ACYCLIC     :   'acyclic';
IRREFLEXIVE :   'irreflexive';
EMPTY       :   'empty';

DOMAIN  :   'domain';
RANGE   :   'range';

EQ      :   '=';
STAR    :   '*';
PLUS    :   '+';
OPT     :   '?';
INV     :   '-1';
NOT     :   '~';
AMP     :   '&';
BAR     :   '|';
SEMI    :   ';';
BSLASH  :   '\\';
POW     :   ('^');

LPAR    :   '(';
RPAR    :   ')';
LBRAC   :   '[';
RBRAC   :   ']';
COMMA   :   ',';
QUOT    :   '"';

NAME    : [A-Za-z0-9\-_.]+;

LINE_COMMENT
    :   '//' ~[\n]*
        -> skip
    ;

BLOCK_COMMENT
    :   '(*' (.)*? '*)'
        -> skip
    ;

WS
    :   [ \t\r\n]+
        -> skip
    ;
//
//INCLUDE
//    :   'include "' .*? '"'
//        -> skip
//    ;

SHOW
    :   'show ' .*? [\r\n]
        -> skip
    ;