grammar Graph;

graph
    :   'digraph' 'G' '{' nodes relations '}'
    ;

nodes
    :   node*
    ;

relations
    :   relation*
    ;

node:   name=ID '[' .*? 'label="' eventID (';' labels)? '"' .*? '];'
    ;

eventID
    :   DigitSequence
    ;

labels
    :   label? (';' label)*
    ;

label
    :   ID
    ;

relation
    :   source=ID '->' target=ID '[' .*? 'label="' label '"' .*? '];'
    ;

ID  :   Letter+ (Letter | Digit)*
    ;

DigitSequence
    :   Digit+
    ;

fragment
Digit
    :   [0-9]
    ;

fragment
Letter
    :   [A-Za-z]
    ;

Whitespace
    :   [ \t]+
        -> skip
    ;

Newline
    :   (   '\r' '\n'?
        |   '\n'
        )
        -> skip
    ;

BlockComment
    :   '(*' .*? '*)'
        -> skip
    ;
