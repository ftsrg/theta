grammar Stmt;

import Expr;

stmt:	assignStmt
    |   memAssignStmt
	|	havocStmt
	|	assumeStmt
	|   skipStmt
	;

stmtList
	:	(stmts+=stmt)(SEMICOLON stmts+=stmt)
	;

skipStmt
    :   'skip'
    ;

assignStmt
	:	LPAREN ASSIGN lhs=ID value=expr RPAREN
	;

memAssignStmt
	:	LPAREN MEMASSIGN derefExpr value=expr RPAREN
	;

havocStmt
	:	LPAREN HAVOC lhs=ID RPAREN
	;

assumeStmt
	:	LPAREN ASSUME cond=expr RPAREN
	;