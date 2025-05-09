// WARNING: this grammar is NOT an official BTOR2 grammar and will accept invalid btor2 circuits.
// Check your circuit with catbtor before using this grammar!
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
    | 'slt' | 'slte' | 'sgt' | 'sgte'
    | 'ult' | 'ulte' | 'ugt' | 'ugte'
    | 'concat' | 'add' | 'mul'
    | 'udiv' | 'urem'
    | 'sdiv' | 'srem' | 'smod'
    | 'saddo' | 'sdivo' | 'smulo' | 'ssubo'
    | 'uaddo' | 'umulo' | 'usubo'
    | 'rol' | 'ror' | 'sll' | 'sra' | 'srl' | 'read';
SYMBOL: ~[ \r\n]+;
COMMENT: ';' ~[\r\n]+;

// Parser rules
btor2: (line '\n')* line ('\n')*;

line: comment | node (symbol)? (comment)?;

comment: COMMENT;

nid: NUM;
sid: NUM;
negNid: (MINUS)? value=nid;

node: ( array_sort | bitvec_sort ) #sort // sort declaration
    | (input | state | init | next | property) #stateful
    | (opidx | op) #operation
    | (filled_constant | constant | constant_d | constant_h) #constantNode;

opidx: ext | slice;

ext: id=nid ('uext'|'sext') sid opd1=nid w=NUM;
slice: id=nid 'slice' sid opd1=nid u=NUM l=NUM;

op: binop | unop | terop;

binop: id=nid BINOP sid opd1=negNid opd2=negNid;
unop: id=nid UNARYOP sid opd1=nid;
terop: id=nid TERNARYOP sid opd1=negNid opd2=nid opd3=nid;

input: id=nid ('input') sid;

init: id=nid 'init' sid param1=nid param2=nid;
next: id=nid 'next' sid param1=nid param2=nid;

state: id=nid 'state' sid;

property: id=nid property_type=('bad' | 'constraint' | 'fair' | 'output' | 'justice' ) param=nid;

array_sort: id=sid 'sort array' sid1=sid sid2=sid;
bitvec_sort: id=sid 'sort bitvec' width=NUM;

constant: id=nid 'const' sid bin=NUM;
constant_d: id=nid 'constd' sid (MINUS)? dec=NUM;
constant_h: id=nid 'consth' sid hex=SYMBOL;
filled_constant: id=nid fill=('one' | 'ones' | 'zero') sid;

symbol: SYMBOL;