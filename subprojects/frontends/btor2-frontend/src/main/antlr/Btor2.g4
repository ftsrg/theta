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

nid: NUM;
sid: NUM;

node: ( array_sort | bitvec_sort ) #sort // sort declaration
    | (input | state | init | next | property) #other
    | (opidx | op) #operation
    | (filled_constant | constant | constant_d | constant_h) #constantNode;
    // | nid 'justice' NUM (nid)+; // justice node // TODO we can not modelcheck justice nodes (not reachability)

opidx: ext | slice;

ext: id=nid ('uext'|'sext') sid opd1=nid w=NUM;
slice: id=nid 'slice' sid opd1=nid u=NUM l=NUM;

op: binop | unop | terop;

binop: id=nid BINOP sid opd1=nid opd2=nid;
unop: id=nid UNARYOP sid opd1=nid;
terop: id=nid TERNARYOP sid opd1=nid opd2=nid opd3=nid;

input: id=nid ('input') sid;

init: id=nid 'init' sid param1=nid param2=nid;
next: id=nid 'next' sid param1=nid param2=nid;

state: id=nid 'state' sid;

property: id=nid ('bad' | 'constraint' | 'fair' | 'output') param=nid;

array_sort: id=sid 'sort array' sid1=sid sid2=sid;
bitvec_sort: id=sid 'sort bitvec' width=NUM; // TODO semantic check for >0

constant: id=nid 'const' sid bin=NUM; // TODO semantic check that really binary
constant_d: id=nid 'constd' sid (MINUS)? dec=NUM; // TODO semantic check that really uint
constant_h: id=nid 'consth' sid hex=SYMBOL; // TODO semantic check that really hex
filled_constant: id=nid ('one' | 'ones' | 'zero') sid;

symbol: SYMBOL;
