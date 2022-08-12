grammar Stmt;

import Expr;

stmt:	assignStmt
	|	havocStmt
	|	assumeStmt
	;

stmtList
	:	(stmts+=stmt)(SEMICOLON stmts+=stmt)
	;

assignStmt
	:	LPAREN ASSIGN lhs=ID value=expr RPAREN
	;

havocStmt
	:	LPAREN HAVOC lhs=ID RPAREN
	;

assumeStmt
	:	LPAREN ASSUME cond=expr RPAREN
	;