lexer grammar CommonTokens;

//// TYPES


BOOLTYPE
	:	'bool' | 'Bool' | 'BOOL'
	;

INTTYPE
	:	'int' | 'Int' | 'INT'
	;

RATTYPE
	:	'rat' | 'Rat' | 'RAT'
	;

BVTYPE
    :   'bv' | 'Bv' | 'BV'
    ;

FPTYPE
    :   'fp' | 'Fp' | 'FP'
    ;

ARRAYINIT
    :   'arrayinit'
    ;

FUNC:   'func' | 'Func' | 'FUNC'
    ;

ARRAY
    :   'array' | 'Array' | 'ARRAY'
    ;

// E X P R E S S I O N S


IF	:	'if'
	;

THEN:	'then'
	;

ELSE:	'else'
	;

IFF	:	'iff'
	;

ITE	:	'ite'
	;

IMPLY
	:	'=>'
	;

FORALL
	:	'forall'
	;

EXISTS
	:	'exists'
	;

OR	:	'or'
	;

AND	:	'and'
	;

XOR	:	'xor'
	;

NOT	:	'not'
	;

EQ	:	'='
	;

NEQ	:	'/='
	;

LT	:	'<'
	;

LEQ	:	'<='
	;

GT	:	'>'
	;

GEQ	:	'>='
	;

PLUS:	'+'
	;

MINUS
	:	'-'
	;

MUL	:	'*'
	;

DIV	:	'div'
	;

MOD	:	'mod'
	;

REM	:	'rem'
	;

PERCENT
	:	'%'
	;

BV_CONCAT
    :   PLUS PLUS
    ;

BV_ZERO_EXTEND
    :   'bv_zero_extend'
    ;

BV_SIGN_EXTEND
    :   'bv_sign_extend'
    ;

BV_ADD
    :   'bvadd'
    ;

BV_SUB
    :   'bvsub'
    ;

BV_POS
    :   'bvpos'
    ;

BV_NEG
    :   'bvneg'
    ;

BV_MUL
    :   'bvmul'
    ;

BV_UDIV
    :   'bvudiv'
    ;

BV_SDIV
    :   'bvsdiv'
    ;

BV_SMOD
    :   'bvsmod'
    ;

BV_UREM
    :   'bvurem'
    ;

BV_SREM
    :   'bvsrem'
    ;

BV_OR
    :   'bvor'
    ;

BV_AND
    :   'bvand'
    ;

BV_XOR
    :   'bvxor'
    ;

BV_NOT
    :   'bvnot'
    ;

BV_SHL
    :   'bvshl'
    ;

BV_ASHR
    :   'bvashr'
    ;

BV_LSHR
    :   'bvlshr'
    ;

BV_ROL
    :   'bvrol'
    ;

BV_ROR
    :   'bvror'
    ;

BV_ULT
    :   'bvult'
    ;

BV_ULE
    :   'bvule'
    ;

BV_UGT
    :   'bvugt'
    ;

BV_UGE
    :   'bvuge'
    ;

BV_SLT
    :   'bvslt'
    ;

BV_SLE
    :   'bvsle'
    ;

BV_SGT
    :   'bvsgt'
    ;

BV_SGE
    :   'bvsge'
    ;

FP_ABS
    :   'fpabs'
    ;

FP_FROM_BV
    :   'fpfrombv' FP_TYPE_DECL (LBRACK ('u' | 's') RBRACK) FP_ROUNDINGMODE?
    ;

FP_IS_INF
    :   'isinfinite'
    ;

FP_IS_NAN
    :   'fpisnan'
    ;

FPMAX
    :   'fpmax'
    ;

FPMIN
    :   'fpmin'
    ;

FPREM
    :   'fprem'
    ;

FPROUNDTOINT
    :   'fproundtoint' FP_ROUNDINGMODE?
    ;

FPSQRT
    :   'fpsqrt' FP_ROUNDINGMODE?
    ;

FPTOBV
    :   'fptobv' BV_TYPE_DECL FP_ROUNDINGMODE?
    ;

FPTOFP
    :   'fptofp' FP_TYPE_DECL FP_ROUNDINGMODE?
    ;

FPSUB
    :   'fpsub'
    ;

FPADD
    :   'fpadd' FP_ROUNDINGMODE?
    ;

FPMUL
    :   'fpmul'
    ;

FPDIV
    :   'fpdiv' FP_ROUNDINGMODE
    ;

FPPOS
    :   'fppos'
    ;

FPNEG
    :   'fpneg'
    ;

TRUE:	'true'
	;

READ:   'read'
    ;

WRITE
    :   'write'
    ;

PRIME
    :   'prime'
    ;

EXTRACT
    :   'extract'
    ;

BV_TYPE_DECL
    :   LBRACK NAT '\'' ('u' | 's') RBRACK
    ;

FP_TYPE_DECL
    :   LBRACK NAT COMMA NAT RBRACK
    ;

FP_ROUNDINGMODE
    :   '[rne]'
    |   '[rna]'
    |   '[rtp]'
    |   '[rtn]'
    |   '[rtz]'
    |   '[RNE]'
    |   '[RNA]'
    |   '[RTP]'
    |   '[RTN]'
    |   '[RTZ]'
    ;

FALSE
	:	'false'
	;

DEFAULT
    :   'default'
    ;

/// STATEMENTS


ASSIGN
	:	'assign'
	;

HAVOC
	:	'havoc'
	;

ASSUME
	:	'assume'
	;

RETURN
	:	'return'
	;


/// BASIC TOKENS


BV  :   NAT '\'b' [0-1]+
    |   '#b' [0-1]+
    |   '#x' [0-1]+
    |   NAT '\'d' (PLUS | MINUS)? INT
    |   NAT '\'x' [0-9a-fA-F]+
    ;

INT	:	SIGN? NAT
	;

NAT	:	DIGIT+
	;

SIGN:	PLUS | MINUS
	;

DOT	:	'.'
	;

ID	:	(LETTER | UNDERSCORE) (LETTER | UNDERSCORE | '$' | DIGIT | COLON)*
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

/// WHITESPACE AND COMMENTS

WS  :  [ \t\r\n\u000C]+ -> skip
    ;

COMMENT
    :   '/*' .*? '*/' -> skip
    ;

LINE_COMMENT
    :   '//' ~[\r\n]* -> skip
    ;

