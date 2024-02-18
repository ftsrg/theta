grammar promela;

spec : module+ EOF;
module : proctype | init | mtype | decl_lst;
separator : ';' | '->';

proctype: ('active' ('[' constant ']')?)? 'proctype' name '(' (decl_lst)? ')' '{' sequence* '}';
init: 'init' '{' sequence* '}';
mtype : 'mtype' ('=' )? '{' name (',' name)* '}' (';')?;
decl_lst : one_decl (';' one_decl)* (';')?;
one_decl: typeID ivar (',' ivar)*;
typeID: 'boolean' | 'int' | 'mtype' | 'chan' | 'short' | 'byte' | 'bit' | 'pid';

sequence: step (separator step)* (';')?;
step : one_decl | stmnt;
ivar: name ('[' any_expr ']')? ('=' any_expr | '=' ch_init)?;

ch_init : '[' any_expr ']' 'of' '{' typeID (',' typeID)* '}';
varref : name ('[' any_expr ']')? ('.' name)?;

send_args: arg_lst | any_expr '(' (arg_lst)? ')';
receive : varref '?' recv_args;
arg_lst : any_expr (',' any_expr)*;
assignx: varref ('=' any_expr | '++' | '--' | '!' send_args | '?' recv_args);

stmnt
    : 'if' ifoption 'fi'
    | 'do' dooption 'od'
    | 'atomic' '{' sequence '}'
    | '{' sequence '}'
    | assignx
    | 'printf' '(' '"' name '"' ')'
    | 'goto' name
    | 'skip'
    | 'break'
    | name ':' stmnt
    | 'run' name '(' (arg_lst)? ')'
    | 'assert' any_expr;

recv_args: recv_arg (',' recv_arg)* | recv_arg '(' recv_args ')';
recv_arg: varref | 'eval' '(' varref ')' | ('-'?) constant;

dooption : ':' ':' (guard '->')? sequence (':' ':' (guard '->')? sequence)*;
ifoption: ':' ':' (guard '->')? sequence (':' ':' (guard '->')? sequence);
guard: any_expr | receive | 'else';

binarop: '+' | '-' | '*' | '/' | '>' ('=')? | '<' ('=')? | '==' | '!=' | '&' ('&')? | MOD | '^' | '||';
unarop: '~' | '-' | '!';

any_expr: '(' any_expr ('->' any_expr ':' any_expr)? ')' (binarop any_expr)?
    | unarop any_expr (binarop any_expr)?
    | 'len' '(' varref ')' (binarop any_expr)?
    | varref ('?' '[' recv_args ']')? (binarop any_expr)?
    | constant (binarop any_expr)?
    | 'timeout' (binarop any_expr)?
    | chanpoll (binarop any_expr)?;

chanpoll: 'full' '(' varref ')'
    | 'empty' '(' varref ')'
    | 'nfull' '(' varref ')'
    | 'nempty' '(' varref ')' ;
name: ID (ID | NUMBER)*;

WS : (' '|'\t'|'\n'|'\r')+ {skip();} ;
ID : ('a'..'z' |'A'..'Z' |'_' )+ ;
NUMBER : '0'..'9'+;
MOD : '%';

constant : 'true' | 'false' | 'skip' | NUMBER;
