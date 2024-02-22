grammar Declarations;

import Type;

decl:	LPAREN name=ID ttype=type RPAREN
	;

declList
	:	(decls+=decl)(COMMA decls+=decl)*
	;
