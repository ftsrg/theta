grammar Boogie;

prog: decl+;

decl: proc | global | impl | constDecl | axiom | func | typeparam | varDecl | typeDef;

typeDef: 'type' ID (typeparam)* ('=' type)? ';';

varDecl: VAR (var (',' var)*)? ';';

proc: PROC ID (typeparam)* '(' (var (',' var)*)? ')' (':' type)? ';'
     'modifies' '(' (ID (',' ID)*)? ')' ';'
     ( 'ensures' exp)? ';'
     ( 'requires' exp)? ';'
     '{' stmt* '}';

global: VAR (var ':=' exp)? (',' var ':=' exp)* ';';

impl: IMPL ID (typeparam)* '(' (var (',' var)*)? ')' (':' type)? ';'
     'modifies' '(' (ID (',' ID)*)? ')' ';'
     ( 'ensures' exp)? ';'
     ( 'requires' exp)? ';'
     '{' stmt* '}';

var: ID (':' type)?;

constDecl: CONST ID (':' type)? (':=' exp)? ';';

axiom: AXIOM exp ';';

func: FUNC ID (typeparam)* '(' (var (',' var)*)? ')' (':' type)? ';'
     '{' stmt* '}';

type: INT_TYPE | BOOL | '[' 'int' ']' type | 'map' '[' type ']' 'to' type | BV | ID;

typeparam: '$' ID (':' type)?;

stmt: ID ':=' exp ';'
     | ID '[' exp   ']:=' exp ';'
     | WHILE '(' exp ')' '{' stmt* '}'
     | IF '(' exp ')' '{' stmt* '}' (ELSE '{' stmt* '}')?
     | CALL ID '(' (exp (',' exp)*)? ')' ';'
     | ASSERT exp ';'
     | ASSUME exp ';'
     | RETURN (exp)? ';'
     | HAVOC ID (',' ID)* ';'
     | FORALL '(' var (',' var)* ')' '{' stmt* '}'
     | GHOST ID ':=' exp ';';

exp: ID
    | ID '(' (exp (',' exp)*)? ')'
    | ID '[' exp ']'
    | exp op exp
    | '(' exp ')'
    | '!' exp
    | OLD '(' exp ')'
    | 'true' | 'false'
    | INT | BV;

op: '&&' | '||' | '==' | '!=' | '<' | '<=' | '>' | '>=' | '+' | '-' | '*' | '/' | 'bvand' | 'bvor' | 'bvxor' | 'bvnot' | 'bvshl' | 'bvlshr' | 'bvashr';

VAR: 'var';
PROC: 'procedure';
IMPL: 'implementation';
CONST: 'constDecl';
AXIOM: 'axiom';
FUNC: 'function';
CALL: 'call';
WHILE: 'while';
IF: 'if';
ELSE: 'else';
ASSERT: 'assert';
ASSUME: 'assume';
RETURN: 'return';
HAVOC: 'havoc';
OLD: 'old';
FORALL: 'forall';
BV: 'bv' [0-9]+;
BOOL: 'bool';
INT_TYPE: 'int';
GHOST: 'ghost';

INT: [0-9]+;
ID: [a-zA-Z_$.][a-zA-Z0-9_.]*;


WS: [ \t\r\n] -> skip;