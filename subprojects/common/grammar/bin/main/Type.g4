grammar Type;

import CommonTokens;

type:	boolType
	|	intType
	|	ratType
	|	funcType
	|	arrayType
	|	bvType
	|   fpType
	;

typeList
	:	(types+=type)(COMMA types+=type)*
	;

boolType
	:	BOOLTYPE
	;

intType
	:	INTTYPE
	;

ratType
	:	RATTYPE
	;

funcType
	:	LPAREN FUNC from=type to=type RPAREN
	;

arrayType
	:	LPAREN ARRAY LPAREN LBRACK indexType=type RBRACK RARROW elemType=type RPAREN RPAREN
	;

bvType
    :   LPAREN BVTYPE size=INT RPAREN
    ;

fpType
    :   LPAREN FPTYPE exponent=INT significand=INT RPAREN
    ;