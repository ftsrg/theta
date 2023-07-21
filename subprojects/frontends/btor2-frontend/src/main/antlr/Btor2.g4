grammar Btor2;

// Lexer rules
WS: [ \t\r\n]+ -> skip;
COMMENT: ';' ~[\r\n]* -> skip;
ID: [a-zA-Z_][a-zA-Z0-9_]*;
NUM: [1-9][0-9]*;
NID: NUM;
SID: NUM;
UINT: [0-9]+;
STRING: '"' ~[\r\n"]* '"';
HEX: '0x' [0-9a-fA-F]+;
PLUS: '+';
MINUS: '-';
OP: 'and' | 'nand' | 'nor' | 'or' | 'xor' | 'iff' | 'implies'
    | 'eq' | 'neq' | 'slt' | 'sle' | 'sgt' | 'sge' | 'ult' | 'ule'
    | 'ugt' | 'uge' | 'concat' | 'add' | 'mul' | 'udiv' | 'urem'
    | 'sdiv' | 'srem' | 'smod' | 'saddo' | 'sdivo' | 'smulo' | 'ssubo'
    | 'rol' | 'ror' | 'sll' | 'sra' | 'srl' | 'read' | 'write' | 'ite';
SORT: 'bitvec' | 'array';
KEYWORD: 'const' | 'constd' | 'consth' | 'input' | 'one' | 'ones'
        | 'zero' | 'state' | 'bad' | 'constraint' | 'fair' | 'output'
        | 'justice' | 'init' | 'next';

// Parser rules
btor2: line+;

line: comment | node (symbol)? comment?;

comment: COMMENT;

node: SID 'sort' ( array_sort | bitvec_sort ) // sort declaration
    | NID (input | state) // input or state declaration
    | NID opidx SID NID NUM (NUM)? // indexed operator node
    | NID op SID NID (NID (NID)?)? // non-indexed operator node
    | NID ('init' | 'next') SID NID NID // init/next node
    | NID ('bad' | 'constraint' | 'fair' | 'output') NID // property node
    | NID 'justice' NUM (NID)+; // justice node

input: 'input' ID
    | 'one' ID
    | 'ones' ID
    | 'zero' ID
    | constant
    | constant_d
    | constant_h;

state: 'state' ID;

array_sort: 'array' ID ID;

bitvec_sort: 'bitvec' NUM;

opidx: '[' (PLUS | MINUS)? UINT ']';

op: OP;

constant: 'const' ID (PLUS | MINUS)? ('0' | '1')+;

constant_d: 'constd' ID (MINUS)? UINT;

constant_h: 'consth' ID HEX;

symbol: STRING;
