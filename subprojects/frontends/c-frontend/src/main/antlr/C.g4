/*
 [The "BSD licence"]
 Copyright (c) 2013 Sam Harwell
 All rights reserved.

 Redistribution and use in source and binary forms, with or without
 modification, are permitted provided that the following conditions
 are met:
 1. Redistributions of source code must retain the above copyright
    notice, this list of conditions and the following disclaimer.
 2. Redistributions in binary form must reproduce the above copyright
    notice, this list of conditions and the following disclaimer in the
    documentation and/or other materials provided with the distribution.
 3. The name of the author may not be used to endorse or promote products
    derived from this software without specific prior written permission.

 THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR
 IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES
 OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.
 IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT,
 INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
 NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
 THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*/

/** C 2011 grammar built from the C11 Spec */
grammar C;


primaryExpression
    :   Identifier                                                          # primaryExpressionId
    |   Constant                                                            # primaryExpressionConstant
    |   StringLiteral+                                                      # primaryExpressionStrings
    |   '(' expression ')'                                                  # primaryExpressionBraceExpression
    //|   genericSelection                                                    # primaryExpressionGenericSelection
    |   '__extension__'? '(' compoundStatement ')'                          # primaryExpressionGccExtension
    //|   '__builtin_va_arg' '(' unaryExpression ',' typeName ')'             # primaryExpressionBuiltinVaArg
    //|   '__builtin_offsetof' '(' typeName ',' unaryExpression ')'           # primaryExpressionBuiltinOffsetof
    ;

//genericSelection
//    :   '_Generic' '(' assignmentExpression ',' genericAssocList ')'
//    ;

//genericAssocList
//    :   genericAssociation (',' genericAssociation)*
//    ;

//genericAssociation
//    :   (typeName | 'default') ':' assignmentExpression
//    ;

postfixExpression
    :   (primaryExpression /*| postfixExpressionExtension*/)
        (postfixExpressionBrackets | postfixExpressionBraces | postfixExpressionMemberAccess
            | postfixExpressionPtrMemberAccess | postfixExpressionIncrement | postfixExpressionDecrement)*
    ;

//postfixExpressionExtension
//    :   '__extension__'? '(' typeName ')' '{' initializerList ','? '}'
//    ;
postfixExpressionBrackets
    :   '[' expression ']'
    ;
postfixExpressionBraces
    :   '(' argumentExpressionList? ')'
    ;
postfixExpressionMemberAccess
    :   '.' Identifier
    ;
postfixExpressionPtrMemberAccess
    :   '->' Identifier
    ;
postfixExpressionIncrement
    :   '++'
    ;
postfixExpressionDecrement
    :   '--'
    ;

argumentExpressionList
    :   assignmentExpression (',' assignmentExpression)*
    ;

unaryExpression
    :
    (unaryExpressionIncrement |  unaryExpressionDecrement /*|  unaryExpressionSizeof*/)*
    (postfixExpression
    |   unaryExpressionCast
    |   unaryExpressionSizeOrAlignOf
//    |   unaryExpressionAddressof // GCC extension address of label
    )
    ;

unaryExpressionIncrement
    :   '++'
    ;
unaryExpressionDecrement
    :   '--'
    ;
//unaryExpressionSizeof
//    :   'sizeof'
//    ;
unaryExpressionCast
    :   unaryOperator castExpression
    ;
unaryExpressionSizeOrAlignOf
    :   ('sizeof' | '_Alignof') '(' typeName ')'
    ;
//unaryExpressionAddressof
//    :   '&&' Identifier
//    ;

unaryOperator
    :   '&' | '*' | '+' | '-' | '~' | '!'
    ;

castExpression
    :   '__extension__'? '(' typeName ')' castExpression    #castExpressionCast
    |   unaryExpression                                     #castExpressionUnaryExpression
//    |   DigitSequence                                       #castExpressionDigitSequence
    ;

multiplicativeExpression
    :   castExpression (signs+=('*'|'/'|'%') castExpression)*
    ;

additiveExpression
    :   multiplicativeExpression (signs+=('+'|'-') multiplicativeExpression)*
    ;

shiftExpression
    :   additiveExpression (signs+=('<<'|'>>') additiveExpression)*
    ;

relationalExpression
    :   shiftExpression (signs+=('<'|'>'|'<='|'>=') shiftExpression)*
    ;

equalityExpression
    :   relationalExpression (signs+=('=='| '!=') relationalExpression)*
    ;

andExpression
    :   equalityExpression ( '&' equalityExpression)*
    ;

exclusiveOrExpression
    :   andExpression ('^' andExpression)*
    ;

inclusiveOrExpression
    :   exclusiveOrExpression ('|' exclusiveOrExpression)*
    ;

logicalAndExpression
    :   inclusiveOrExpression ('&&' inclusiveOrExpression)*
    ;

logicalOrExpression
    :   logicalAndExpression ( '||' logicalAndExpression)*
    ;

conditionalExpression
    :   logicalOrExpression ('?' expression ':' conditionalExpression)?
    ;

assignmentExpression
    :   conditionalExpression                                   #assignmentExpressionConditionalExpression
    |   unaryExpression assignmentOperator assignmentExpression #assignmentExpressionAssignmentExpression
//    |   DigitSequence                                           #assignmentExpressionDigitSequence
    ;

assignmentOperator
    :   '=' | '*=' | '/=' | '%=' | '+=' | '-=' | '<<=' | '>>=' | '&=' | '^=' | '|='
    ;

expression
    :   assignmentExpression (',' assignmentExpression)*
    ;

constantExpression
    :   conditionalExpression
    ;

declaration
    :   declarationSpecifiers initDeclaratorList? ';'
//    |   staticAssertDeclaration                         # declarationStatic
    ;

declarationSpecifiers
    :   declarationSpecifier+
    ;

declarationSpecifiers2
    :   declarationSpecifier+
    ;

declarationSpecifier
    :   storageClassSpecifier
    |   typeSpecifierPointer
    |   typeSpecifier
    |   typeQualifier
    |   functionSpecifier
    |   alignmentSpecifier
    ;

initDeclaratorList
    :   initDeclarator (',' initDeclarator)*
    ;

initDeclarator
    :   declarator ('=' initializer)?
    ;

storageClassSpecifier
    :   'typedef'
    |   'extern'
    |   'static'
    |   '_Thread_local'
    |   'auto'
    |   'register'
    ;

typeSpecifier
    :   ('void'
    |   'char'
    |   'short'
    |   'int'
    |   'long'
    |   'signed'
    |   'unsigned'
    |   '_Bool'
    |   '_Complex'
    |   '__m128'
    |   '__m128d'
    |   '__m128i')                                                  # typeSpecifierSimple
    |   '__thread'                                                  # typeSpecifierGccThread
    |   'float'                                                     # typeSpecifierFloat
    |   'double'                                                    # typeSpecifierDouble
    |   '__extension__' '(' ('__m128' | '__m128d' | '__m128i') ')'  # typeSpecifierExtension
    |   atomicTypeSpecifier                                         # typeSpecifierAtomic
    |   structOrUnionSpecifier                                      # typeSpecifierCompound
    |   enumSpecifier                                               # typeSpecifierEnum
    |   typedefName                                                 # typeSpecifierTypedefName
    |   '__typeof__' '(' constantExpression ')'                     # typeSpecifierTypeof
//    |   typeSpecifier pointer                                       # typeSpecifierPointer
    ;

typeSpecifierPointer
    :   typeSpecifier pointer
    ;

structOrUnionSpecifier
    :   structOrUnion Identifier? '{' structDeclarationList '}'     # compoundDefinition
    |   structOrUnion Identifier                                    # compoundUsage
    ;

structOrUnion
    :   'struct'
    |   'union'
    ;

structDeclarationList
    :   structDeclaration+
    ;

structDeclaration
    :   specifierQualifierList structDeclaratorList? ';'
//    |   staticAssertDeclaration                             #structDeclarationStatic
    ;

specifierQualifierList
    :   typeSpecifierOrQualifier+ typeSpecifierPointer
    |   typeSpecifierOrQualifier+
    ;

typeSpecifierOrQualifier
    :   typeSpecifier
    |   typeQualifier
    ;

structDeclaratorList
    :   structDeclarator (',' structDeclarator)*
    ;

structDeclarator
    :   declarator                          #structDeclaratorSimple
    |   declarator? ':' constantExpression  #structDeclaratorConstant
    ;

enumSpecifier
    :   'enum' Identifier? '{' enumeratorList ','? '}' #enumDefinition
    |   'enum' Identifier                              #enumUsage
    ;

enumeratorList
    :   enumerator (',' enumerator)*
    ;

enumerator
    :   enumerationConstant ('=' constantExpression)?
    ;

enumerationConstant
    :   Identifier
    ;

atomicTypeSpecifier
    :   '_Atomic' '(' typeName ')'
    ;

typeQualifier
    :   'const'
    |   'restrict'
    |   'volatile'
    |   '_Atomic'
    ;

functionSpecifier
    :   ('inline'
    |   '_Noreturn'
    |   '__inline__' // GCC extension
    |   '__stdcall')
    |   gccAttributeSpecifier
    |   '__declspec' '(' Identifier ')'
    ;

alignmentSpecifier
    :   '_Alignas' '(' (typeName | constantExpression) ')'
    ;

declarator
    :   pointer? directDeclarator gccDeclaratorExtension*
    ;

directDeclarator
    :   Identifier                                                                  # directDeclaratorId
    |   '(' declarator ')'                                                          # directDeclaratorBraces
    |   directDeclarator '[' typeQualifierList? assignmentExpression? ']'           # directDeclaratorArray1
    |   directDeclarator '[' 'static' typeQualifierList? assignmentExpression ']'   # directDeclaratorArray2
    |   directDeclarator '[' typeQualifierList 'static' assignmentExpression ']'    # directDeclaratorArray3
    |   directDeclarator '[' typeQualifierList? '*' ']'                             # directDeclaratorArray4
    |   directDeclarator '(' parameterTypeList? ')'                                 # directDeclaratorFunctionDecl
//    |   directDeclarator '(' identifierList? ')'                                    # directDeclaratorFunctionCall
    |   Identifier ':' DigitSequence                                                # directDeclaratorBitField
//    |   '(' typeSpecifier? pointer directDeclarator ')'                             # directDeclaratorFunctionPointer
    ;

gccDeclaratorExtension
    :   ('__asm' | '__asm__') '(' StringLiteral+ ')'
    |   gccAttributeSpecifier
    ;

gccAttributeSpecifier
    :   '__attribute__' '(' '(' gccAttributeList ')' ')'
    ;

gccAttributeList
    :   gccAttribute? (',' gccAttribute?)*
    ;

gccAttribute
    :   ~(',' | '(' | ')') // relaxed def for "identifier or reserved word"
        ('(' argumentExpressionList? ')')?
    ;

nestedParenthesesBlock
    :   (   ~('(' | ')')
        |   '(' nestedParenthesesBlock ')'
        )*
    ;

pointer
    :  ((stars+='*'|'^') ('__restrict')? typeQualifierList?)+ // ^ - Blocks language extension
    ;

typeQualifierList
    :   typeQualifier+
    ;

parameterTypeList
    :   parameterList (',' ellipses='...')?
    ;

parameterList
    :   parameterDeclaration (',' parameterDeclaration)*
    ;

parameterDeclaration
    :   declarationSpecifiers declarator            # ordinaryParameterDeclaration
    |   declarationSpecifiers2 abstractDeclarator?  # abstractParameterDeclaration
    ;

//identifierList
//    :   Identifier (',' Identifier)*
//    ;

typeName
    :   specifierQualifierList abstractDeclarator?
    ;

abstractDeclarator
    :   pointer
    |   pointer? directAbstractDeclarator gccDeclaratorExtension*
    ;

directAbstractDeclarator
    :   '(' abstractDeclarator ')' gccDeclaratorExtension*
    |   '[' typeQualifierList? assignmentExpression? ']'
    |   '[' 'static' typeQualifierList? assignmentExpression ']'
    |   '[' typeQualifierList 'static' assignmentExpression ']'
    |   '[' '*' ']'
    |   '(' parameterTypeList? ')' gccDeclaratorExtension*
    |   directAbstractDeclarator '[' typeQualifierList? assignmentExpression? ']'
    |   directAbstractDeclarator '[' 'static' typeQualifierList? assignmentExpression ']'
    |   directAbstractDeclarator '[' typeQualifierList 'static' assignmentExpression ']'
    |   directAbstractDeclarator '[' '*' ']'
    |   directAbstractDeclarator '(' parameterTypeList? ')' gccDeclaratorExtension*
    ;

typedefName
    :   Identifier
    ;

initializer
    :   assignmentExpression
    |   '{' initializerList ','? '}'
    ;

initializerList
    :   designation? initializers+=initializer (',' designation? initializers+=initializer)*
    ;

designation
    :   designatorList '='
    ;

designatorList
    :   designator+
    ;

designator
    :   '[' constantExpression ']'
    |   '.' Identifier
    ;

//staticAssertDeclaration
//    :   '_Static_assert' '(' constantExpression ',' StringLiteral+ ')' ';'
//    ;

statement
    :   labeledStatement
    |   compoundStatement
    |   expressionStatement
    |   selectionStatement
    |   iterationStatement
    |   jumpStatement ';'
//    |   ('__asm' | '__asm__') ('volatile' | '__volatile__') '(' (logicalOrExpression (',' logicalOrExpression)*)? (':' (logicalOrExpression (',' logicalOrExpression)*)?)* ')' ';'
    ;

labeledStatement
    :   Identifier ':' statement                # identifierStatement
    |   'case' constantExpression ':' statement # caseStatement
    |   'default' ':' statement                 # defaultStatement
    ;

compoundStatement
    :   '{' blockItemList? '}'
    ;

blockItemList
    :   blockItem+
    ;

blockItem
    :   statement       # bodyStatement
    |   declaration     # bodyDeclaration
    ;

expressionStatement
    :   expression? ';'
    ;

selectionStatement
    :   'if' '(' expression ')' statement ('else' statement)?   #ifStatement
    |   'switch' '(' expression ')' statement                   #switchStatement
    ;

iterationStatement
    :   While '(' expression ')' statement                      # whileStatement
    |   Do statement While '(' expression ')' ';'               # doWhileStatement
    |   For '(' forCondition ')' statement                      # forStatement
    ;

//    |   'for' '(' expression? ';' expression?  ';' forUpdate? ')' statement
//    |   For '(' declaration  expression? ';' expression? ')' statement

forCondition
	:   forInit ';' forTest ';' forIncr
	;

forInit
    :  forDeclaration
    |  expression?
    ;

forTest
    :   forExpression?
    ;

forIncr
    :   forExpression?
    ;

forDeclaration
    :   declarationSpecifiers initDeclaratorList?
    ;

forExpression
    :   assignmentExpression (',' assignmentExpression)*
    ;

jumpStatement
    :   'goto' Identifier       # gotoStatement
    |   'continue'              # continueStatement
    |   'break'                 # breakStatement
    |   'return' expression?    # returnStatement
//    |   'goto' unaryExpression // GCC extension
    ;

compilationUnit
    :   translationUnit? EOF
    ;

translationUnit
    :   externalDeclaration+
    ;

externalDeclaration
    :   functionDefinition  #externalFunctionDefinition
    |   declaration         #globalDeclaration
    |   ';'                 #externalNop
    ;

functionDefinition
    :   declarationSpecifiers declarator /*declarationList?*/ compoundStatement
    ;

//declarationList
//    :   declaration+
//    ;

Extension: '__extension__' -> skip; // Hack to make .i files work (SV-COMP)
VoidSizeof: '(void) sizeof' -> skip; // Hack to make .i files work (SV-COMP)
Auto : 'auto';
Break : 'break';
Case : 'case';
Char : 'char';
Const : 'const';
Continue : 'continue';
Default : 'default';
Do : 'do';
Double : 'double';
Else : 'else';
Enum : 'enum';
Extern : 'extern';
Float : 'float';
For : 'for';
Goto : 'goto';
If : 'if';
Inline : 'inline';
Int : 'int';
Long : 'long';
Register : 'register';
Restrict : 'restrict';
Return : 'return';
Short : 'short';
Signed : 'signed';
Sizeof : 'sizeof';
Static : 'static';
Struct : 'struct';
Switch : 'switch';
Typedef : 'typedef';
Union : 'union';
Unsigned : 'unsigned';
Void : 'void';
Volatile : 'volatile';
While : 'while';

Alignas : '_Alignas';
Alignof : '_Alignof';
Atomic : '_Atomic';
Bool : '_Bool';
Complex : '_Complex';
Generic : '_Generic';
Imaginary : '_Imaginary';
Noreturn : '_Noreturn';
StaticAssert : '_Static_assert';
ThreadLocal : '_Thread_local';

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

Question : '?';
Colon : ':';
Semi : ';';
Comma : ',';

Assign : '=';
// '*=' | '/=' | '%=' | '+=' | '-=' | '<<=' | '>>=' | '&=' | '^=' | '|='
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
Ellipsis : '...';

Identifier
    :   IdentifierNondigit
        (   IdentifierNondigit
        |   Digit
        |   '$'
        )*
    ;

fragment
IdentifierNondigit
    :   Nondigit
    |   UniversalCharacterName
    //|   // other implementation-defined characters...
    ;

fragment
Nondigit
    :   [a-zA-Z_]
    ;

fragment
Digit
    :   [0-9]
    ;

fragment
UniversalCharacterName
    :   '\\u' HexQuad
    |   '\\U' HexQuad HexQuad
    ;

fragment
HexQuad
    :   HexadecimalDigit HexadecimalDigit HexadecimalDigit HexadecimalDigit
    ;

Constant
    :   IntegerConstant
    |   FloatingConstant
    //|   EnumerationConstant
    |   CharacterConstant
    ;

fragment
IntegerConstant
    :   DecimalConstant IntegerSuffix?
    |   OctalConstant IntegerSuffix?
    |   HexadecimalConstant IntegerSuffix?
    |	BinaryConstant
    ;

fragment
BinaryConstant
	:	'0' [bB] [0-1]+
	;

fragment
DecimalConstant
    :   NonzeroDigit Digit*
    ;

fragment
OctalConstant
    :   '0' OctalDigit*
    ;

fragment
HexadecimalConstant
    :   HexadecimalPrefix HexadecimalDigit+
    ;

fragment
HexadecimalPrefix
    :   '0' [xX]
    ;

fragment
NonzeroDigit
    :   [1-9]
    ;

fragment
OctalDigit
    :   [0-7]
    ;

fragment
HexadecimalDigit
    :   [0-9a-fA-F]
    ;

fragment
IntegerSuffix
    :   UnsignedSuffix LongSuffix?
    |   UnsignedSuffix LongLongSuffix
    |   LongSuffix UnsignedSuffix?
    |   LongLongSuffix UnsignedSuffix?
    ;

fragment
UnsignedSuffix
    :   [uU]
    ;

fragment
LongSuffix
    :   [lL]
    ;

fragment
LongLongSuffix
    :   'll' | 'LL'
    ;

fragment
FloatingConstant
    :   DecimalFloatingConstant
    |   HexadecimalFloatingConstant
    ;

fragment
DecimalFloatingConstant
    :   FractionalConstant ExponentPart? FloatingSuffix?
    |   DigitSequence ExponentPart FloatingSuffix?
    ;

fragment
HexadecimalFloatingConstant
    :   HexadecimalPrefix (HexadecimalFractionalConstant | HexadecimalDigitSequence) BinaryExponentPart FloatingSuffix?
    ;

fragment
FractionalConstant
    :   DigitSequence? '.' DigitSequence
    |   DigitSequence '.'
    ;

fragment
ExponentPart
    :   [eE] Sign? DigitSequence
    ;

fragment
Sign
    :   [+-]
    ;

DigitSequence
    :   Digit+
    ;

fragment
HexadecimalFractionalConstant
    :   HexadecimalDigitSequence? '.' HexadecimalDigitSequence
    |   HexadecimalDigitSequence '.'
    ;

fragment
BinaryExponentPart
    :   [pP] Sign? DigitSequence
    ;

fragment
HexadecimalDigitSequence
    :   HexadecimalDigit+
    ;

fragment
FloatingSuffix
    :   [flFL]
    ;

fragment
CharacterConstant
    :   '\'' CCharSequence '\''
    |   'L\'' CCharSequence '\''
    |   'u\'' CCharSequence '\''
    |   'U\'' CCharSequence '\''
    ;

fragment
CCharSequence
    :   CChar+
    ;

fragment
CChar
    :   ~['\\\r\n]
    |   EscapeSequence
    ;

fragment
EscapeSequence
    :   SimpleEscapeSequence
    |   OctalEscapeSequence
    |   HexadecimalEscapeSequence
    |   UniversalCharacterName
    ;

fragment
SimpleEscapeSequence
    :   '\\' ['"?abfnrtv\\]
    ;

fragment
OctalEscapeSequence
    :   '\\' OctalDigit OctalDigit? OctalDigit?
    ;

fragment
HexadecimalEscapeSequence
    :   '\\x' HexadecimalDigit+
    ;

StringLiteral
    :   EncodingPrefix? '"' SCharSequence? '"'
    ;

fragment
EncodingPrefix
    :   'u8'
    |   'u'
    |   'U'
    |   'L'
    ;

fragment
SCharSequence
    :   SChar+
    ;

fragment
SChar
    :   ~["\\\r\n]
    |   EscapeSequence
    |   '\\\n'   // Added line
    |   '\\\r\n' // Added line
    ;

ComplexDefine
    :   '#' Whitespace? 'define'  ~[#\r\n]*
        -> skip
    ;

IncludeDirective
    :   '#' Whitespace? 'include' Whitespace? (('"' ~[\r\n]* '"') | ('<' ~[\r\n]* '>' )) Whitespace? Newline
        -> skip
    ;

// ignore the following asm blocks:
/*
    asm
    {
        mfspr x, 286;
    }
 */
AsmBlock
    :   'asm' ~'{'* '{' ~'}'* '}'
	-> skip
    ;

// ignore the lines generated by c preprocessor
// sample line : '#line 1 "/home/dm/files/dk1.h" 1'
LineAfterPreprocessing
    :   '#line' Whitespace* ~[\r\n]*
        -> skip
    ;

LineDirective
    :   '#' Whitespace? DecimalConstant Whitespace? StringLiteral ~[\r\n]*
        -> skip
    ;

PragmaDirective
    :   '#' Whitespace? 'pragma' Whitespace ~[\r\n]*
        -> skip
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
    :   '/*' .*? '*/'
        -> skip
    ;

LineComment
    :   '//' ~[\r\n]*
        -> skip
    ;

WORD
    : [a-zA-Z_]+ -> skip
    ;
