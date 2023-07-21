grammar Btor2;

// Lexer rules
WS: [ ]+ -> skip;
NUM: [0-9]+;
PLUS: '+';
MINUS: '-';
UNARYOP: 'not'
         | 'inc' | 'dec' | 'neg'
         | 'redand' | 'redor' | 'redxor';
TERNARYOP: 'ite' | 'write';
BINOP: 'and' | 'nand' | 'nor' | 'or' | 'xor' | 'iff' | 'implies'
    | 'eq' | 'neq'
    | 'slt' | 'sle' | 'sgt' | 'sgte'
    | 'ult' | 'ule' | 'ugt' | 'ugte'
    | 'concat' | 'add' | 'mul'
    | 'udiv' | 'urem'
    | 'sdiv' | 'srem' | 'smod'
    | 'saddo' | 'sdivo' | 'smulo' | 'ssubo'
    | 'uaddo' | 'umulo' | 'usubo'
    | 'rol' | 'ror' | 'sll' | 'sra' | 'srl' | 'read';
SYMBOL: ~[ \r\n]+;
COMMENT: ';' ~[\r\n]+;

// Parser rules
btor2: line+;

line: ( comment | node (symbol)? (comment)? ) '\n';

comment: COMMENT;

nid: NUM; // TODO semantic check nid/sid for >0
sid: NUM; // TODO semantic check nid/sid for >0

node: ( array_sort | bitvec_sort ) // sort declaration
    | (input | state) // input or state declaration
    | opidx // indexed operator node
    | op // non-indexed operator node
    | (init | next) // init/next node
    | property; // property node
    // | nid 'justice' NUM (nid)+; // justice node // TODO we can not model check justice nodes (not reachability)

opidx: ext | slice;

ext: nid ('uext'|'sext') sid nid w=NUM;
slice: nid 'slice' sid nid u=NUM l=NUM;

op: binop | unop | terop;

binop: nid BINOP sid opd1=nid opd2=nid;
unop: nid UNARYOP sid opd1=nid;
terop: nid TERNARYOP sid opd1=nid opd2=nid opd3=nid;

input: nid ('input' sid
    | 'one' sid
    | 'ones' sid
    | 'zero' sid
    | constant
    | constant_d
    | constant_h);

init: nid 'init' sid nid nid;
next: nid 'next' sid nid nid;

state: nid 'state' sid;

property: nid ('bad' | 'constraint' | 'fair' | 'output') nid;

array_sort: sid 'sort array' sid sid;
bitvec_sort: sid 'sort bitvec' NUM; // TODO semantic check for >0

constant: 'const' sid bin=NUM; // TODO semantic check that really binary

constant_d: 'constd' sid (MINUS)? dec=NUM; // TODO semantic check that really uint

constant_h: 'consth' sid hex=SYMBOL; // TODO semantic check that really hex

symbol: SYMBOL;
