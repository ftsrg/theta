// WARNING only works on PREPROCESSSED promela files (no #define)
// use cpp -p to preprocess promela file with macros
grammar promela;

spec    : (module(Separator)*)+;

module  : proctype
        | init
        | never
        | trace
        | utype
        | mtype
        | decl_lst;

proctype
    : (active)? 'proctype' Name '(' (decl_lst)? ')' (priority)? (enabler)? '{' sequence '}';

init    : 'init' (priority)? '{' sequence '}';

never   : 'never' '{' sequence '}';

trace   : 'trace' '{' sequence '}';

utype   : 'typedef' Name '{' decl_lst '}';

mtype   : 'mtype' '='? '{' Name (',' Name)* '}';

decl_lst: one_decl (Separator one_decl)*;

one_decl
    : (visible)? typename ivar (',' ivar)*
    | (visible)? unsigned_decl;

unsigned_decl
    : 'unsigned' Name ':' Const('=' any_expr)?;

typename
    : 'bit' | 'bool' | 'byte' | 'short' | 'int' | 'mtype' | 'chan' | Name;

active  : 'active' '['Const']';

priority: 'priority' Const;

enabler : 'provided' '(' expr ')';

visible : 'hidden' | 'show';

sequence: step (Separator step)*;

step    : stmnt ('unless' stmnt)?
        | decl_lst
        | ('xr') varref (',' varref)*
        | ('xs') varref (',' varref)*;

ivar    : Name ('['Const']')? (('=' any_expr)|('=' ch_init))?;

ch_init : '['Const']' 'of' '{' typename (',' typename)* '}';

varref  : Name ('[' any_expr ']')? ('.' varref)?;

send    : varref '!' send_args
        | varref '!!' send_args;

receive : varref '?' recv_args
        | varref '??' recv_args
        | varref '?' '<' recv_args '>'
        | varref '??' '<' recv_args '>';

poll    : varref '?' '[' recv_args ']'
        | varref '??' '[' recv_args ']';

send_args: arg_lst | any_expr '(' arg_lst ')';

arg_lst : any_expr (',' any_expr)*;

recv_args: recv_arg (',' recv_arg)* | recv_arg '(' recv_args ')';

recv_arg: varref | 'eval' '(' varref ')' | ('-')? Const;

assign  : varref '=' any_expr
        | varref '++'
        | varref '--';

stmnt   : 'if' promela_options 'fi'
        | 'do' promela_options 'od'
        | 'for' '(' range ')' '{' sequence '}'
        | 'atomic' '{' sequence '}'
        | 'd_step' '{' sequence '}'
        | 'select' '(' range ')'
        | '{' sequence '}'
        | send
        | receive
        | assign
        | 'else'
        | 'break'
        | 'goto' Name
        | Name ':' stmnt
        | 'print' '(' String (',' arg_lst)? ')'
        | 'assert' expr
        | expr;

range   : Name ':' any_expr '..' any_expr
        | Name 'in' Name;

promela_options : ('::' sequence)+;

andor   : '&&' | '||';

binarop : '+' | '-' | '*' | '/' | '%'
        | '&' | '^' | '|'
        | '>' | '<' | '>=' | '<=' | '==' | '!='
        | '<<' | '>>' | andor;

unarop  : '~' | '-' | '!';

any_expr: '(' any_expr ')'
        | any_expr binarop any_expr
        | unarop any_expr
        | '(' any_expr '->' any_expr ':' any_expr ')'
        | 'len' '(' varref ')'
        | poll
        | varref
        | Const
        | 'timeout'
        | 'np_'
        | 'enabled' '(' any_expr ')'
        | 'pc_value' '(' any_expr ')'
        | Name '[' any_expr ']' '@' Name
        | 'run' Name '(' (arg_lst)? ')' (priority)?
        | 'get_priority' '(' expr ')'
        | 'set_priority' '(' expr ',' expr ')';

expr    : any_expr
        | '(' expr ')'
        | expr andor expr
        | chanpoll '(' varref ')';

chanpoll: 'full' | 'empty' | 'nfull' | 'nempty';

String  : '"' ~["]* '"';

Name    : Alpha (Alpha|Number)*;

Const   : 'true' | 'false' | 'skip' | (Number)+;

Alpha   : [a-zA-Z_]; // grammar is case insensitive, A-Z is superfluous

Number  : [0-9];

LeftParen : '(';
RightParen : ')';
LeftBracket : '[';
RightBracket : ']';
LeftBrace : '{';
RightBrace : '}';

Less : '<';
LessEqual : '<=';
Greater : '>';
GreaterEqual : '>=';
LeftShift : '<<';
RightShift : '>>';

Plus : '+';
PlusPlus : '++';
Minus : '-';
MinusMinus : '--';
Star : '*';
Div : '/';
Mod : '%';

And : '&';
Or : '|';
AndAnd : '&&';
OrOr : '||';
Caret : '^';
Not : '!';
Tilde : '~';

Separator: Semi | Arrow;

Question : '?';
Colon : ':';
DoubleColon : Colon Colon;
Semi : ';';
Comma : ',';

Assign : '=';
StarAssign : '*=';
DivAssign : '/=';
ModAssign : '%=';
PlusAssign : '+=';
MinusAssign : '-=';
LeftShiftAssign : '<<=';
RightShiftAssign : '>>=';
AndAssign : '&=';
XorAssign : '^=';
OrAssign : '|=';

Equal : '==';
NotEqual : '!=';

Arrow : '->';
Dot : '.';
Underscore : '_';

COMMENT
    :   '#' ~[\r\n]* -> skip // Match and skip comments starting with '#'
    ;

WS
    :   [ \t\n]+
        -> skip
    ;