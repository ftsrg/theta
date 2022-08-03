grammar LitmusAArch64;

import LitmusAssertions;

main
    :    LitmusLanguage ~(LBrace)* variableDeclaratorList program variableList? assertionFilter? assertionList? EOF
    ;

variableDeclaratorList
    :   LBrace variableDeclarator? (Semi variableDeclarator)* Semi? RBrace Semi?
    ;

variableDeclarator
    :   variableDeclaratorLocation
    |   variableDeclaratorRegister
    |   variableDeclaratorRegisterLocation
    |   variableDeclaratorLocationLocation
    ;

variableDeclaratorLocation
    :   location Equals constant
    ;

variableDeclaratorRegister
    :   threadId Colon register64 Equals constant
    ;

variableDeclaratorRegisterLocation
    :   threadId Colon register64 Equals Amp? location
    ;

variableDeclaratorLocationLocation
    :   location Equals Amp? location
    ;

variableList
    :   Locations LBracket variable (Semi variable)* Semi? RBracket
    ;

variable
    :   location
    |   threadId Colon register64
    ;

program
    :   threadDeclaratorList instructionList
    ;

threadDeclaratorList
    :   threadId (Bar threadId)* Semi
    ;

instructionList
    :   (instructionRow)+
    ;

instructionRow
    :   instruction (Bar instruction)* Semi
    ;

instruction
    :   simpleInstruction
    |   branch
    |   branchRegister
    |   branchLabel
    |   exclusiveInstruction
    ;

simpleInstruction
    :
    |   mov
    |   arithmetic
    |   load
    |   store
    |   cmp
    |   fence
    ;

exclusiveInstruction
    :   loadExclusive
    |   storeExclusive
    ;

mov
    :   MovInstruction r32 = register32 Comma expr32 #mov32
    |   MovInstruction r64 = register64 Comma expr64 #mov64
    ;

cmp
    :   CmpInstruction r32 = register32 Comma expr32 #cmp32
    |   CmpInstruction r64 = register64 Comma expr64 #cmp64
    ;

arithmetic
    :   arithmeticInstruction rD32 = register32 Comma rV32 = register32 Comma expr32 #arith32
    |   arithmeticInstruction rD64 = register64 Comma rV64 = register64 Comma expr64 #arith64
    ;

load
    :   loadInstruction rD32 = register32 Comma LBracket address (Comma offset)? RBracket #load32
    |   loadInstruction rD64 = register64 Comma LBracket address (Comma offset)? RBracket #load64
    ;

loadExclusive
    :   loadExclusiveInstruction rD32 = register32 Comma LBracket address (Comma offset)? RBracket #loadX32
    |   loadExclusiveInstruction rD64 = register64 Comma LBracket address (Comma offset)? RBracket #loadX64
    ;

store
    :   storeInstruction rV32 = register32 Comma LBracket address (Comma offset)? RBracket #store32
    |   storeInstruction rV64 = register64 Comma LBracket address (Comma offset)? RBracket #store64
    ;

storeExclusive
    :   storeExclusiveInstruction rS32 = register32 Comma rV32 = register32 Comma LBracket address (Comma offset)? RBracket #storeX32
    |   storeExclusiveInstruction rS32 = register32 Comma rV64 = register64 Comma LBracket address (Comma offset)? RBracket #storeX64
    ;

fence
    :   Fence
    |   Fence FenceOpt
    ;

branch
    :   BranchInstruction (Period branchCondition)? label
    ;

branchRegister
    :   branchRegInstruction rV32 = register32 Comma label #branchRegister32
    |   branchRegInstruction rV64 = register64 Comma label #branchRegister64
    ;

branchLabel
    :   label Colon
    ;

loadInstruction locals [String mo]
    :   LDR     {$mo = "RX";}
    |   LDAR    {$mo = "A";}
    ;

loadExclusiveInstruction locals [String mo]
    :   LDXR    {$mo = "RX";}
    |   LDAXR   {$mo = "A";}
    ;

storeInstruction locals [String mo]
    :   STR     {$mo = "RX";}
    |   STLR    {$mo = "L";}
    ;

storeExclusiveInstruction locals [String mo]
    :   STXR    {$mo = "RX";}
    |   STLXR   {$mo = "L";}
    ;

arithmeticInstruction
    :   ADD #addInstruction
//    |   ADDS    { throw new RuntimeException("Instruction ADDS is not implemented"); }
    |   SUB #subInstruction
//    |   SUBS    { throw new RuntimeException("Instruction SUBS is not implemented"); }
//    |   ADC     { throw new RuntimeException("Instruction ADC is not implemented"); }
//    |   ADCS    { throw new RuntimeException("Instruction ADCS is not implemented"); }
//    |   SBC     { throw new RuntimeException("Instruction SBC is not implemented"); }
//    |   SBCS    { throw new RuntimeException("Instruction SBCS is not implemented"); }
    |   AND #andInstruction
    |   ORR #orrInstruction
    |   EOR #eorInstruction
//    |   BIC     { throw new RuntimeException("Instruction BIC is not implemented"); }
//    |   ORN     { throw new RuntimeException("Instruction ORN is not implemented"); }
//    |   EON     { throw new RuntimeException("Instruction EON is not implemented"); }
    ;

branchCondition
    :   EQ #eqCondition
    |   NE #neCondition
    |   GE #geCondition
    |   LE #leCondition
    |   GT #gtCondition
    |   LT #ltCondition
//    |   CS
//    |   HS
//    |   CC
//    |   LO
//    |   MI
//    |   PL
//    |   VS
//    |   VC
//    |   HI
//    |   LS
//    |   AL
    ;

branchRegInstruction locals [boolean zerotest]
    :   CBZ  {$zerotest = true;}
    |   CBNZ {$zerotest = false;}
    ;

//shiftOperator
//    :   LSL #lslOperator
//    |   LSR #lsrOperator
//    |   ASR #asrOperator
//    ;

expr64
    :   expressionRegister64
    |   expressionImmediate64
    |   expressionConversion
    ;

expr32
    :   expressionRegister32
    |   expressionImmediate32
    ;

expressionImmediate64
    :   expressionImmediate
    ;

expressionImmediate32
    :   expressionImmediate
    ;

offset
    :   immediate
    |   expressionConversion
    ;

//shift
//    :   Comma shiftOperator immediate
//    ;

expressionRegister64
    :   register64// shift?
    ;

expressionRegister32
    :   register32// shift?
    ;

expressionImmediate
    :   immediate// shift?
    ;

expressionConversion
    :   register32 Comma BitfieldOperator
    ;

address returns[String id]
    :   r = register64 {$id = $r.id;}
    ;

register64 returns[String id]
    :   r = Register64 {$id = $r.text;}
    ;

register32 returns[String id]
    :   r = Register32 {$id = $r.text.replace("W","X");}
    ;

location
    :   Identifier
    ;

immediate
    :   Num constant
    ;

label
    :   Identifier
    ;

assertionValue
    :   location
    |   threadId Colon register64
    |   constant
    ;

Locations
    :   'locations'
    ;

// Arthmetic instructions

ADD     :   'ADD'   ;   // Add
ADDS    :   'ADDS'  ;   // Add and set flag
SUB     :   'SUB'   ;   // Sub
SUBS    :   'SUBS'  ;   // Sub and set flag
ADC     :   'ADC'   ;   // Add and use carry flag
ADCS    :   'ADCS'  ;   // Add and use carry flag and set carry flag
SBC     :   'SBC'   ;   // Sub and use carry flag
SBCS    :   'SBCS'  ;   // Sub and use carry flag and set carry flag
AND     :   'AND'   ;   // Logical AND
ORR     :   'ORR'   ;   // Logical OR
EOR     :   'EOR'   ;   // Logical XOR
BIC     :   'BIC'   ;   // Invert and AND (Bitwise Bit Clear)
ORN     :   'ORN'   ;   // Invert and OR
EON     :   'EON'   ;   // Invert and XOR

// Load instructions

LDR    :   'LDR'    ;
LDAR   :   'LDAR'   ;
LDXR   :   'LDXR'   ;
LDAXR  :   'LDAXR'  ;

// Store instructions

STR    :   'STR'    ;
STLR   :   'STLR'   ;
STXR   :   'STXR'   ;
STLXR  :   'STLXR'   ;

MovInstruction
    :   'MOV'
    ;

CmpInstruction
    :   'CMP'
    ;

BranchInstruction
    :   'B'
    ;

Fence
    :   'DMB'
    |   'DSB'
    |   'ISB'
    ;

FenceOpt
    :   'SY'    |   'sy'        // Full barrier (default)
    |   'LD'    |   'ld'        // Loads only
    |   'ST'    |   'st'        // Stores only
    |   'ISHLD' |   'ishld'     // Loads only and inner sharable domain only
    |   'NSHLD' |   'nshld'     // Loads only and out to the point of unification only
    |   'OSHLD' |   'oshld'     // Loads only and outer sharable domain only
    |   'ISHST' |   'ishsd'     // Stores only and inner sharable domain only
    |   'NSHST' |   'nshst'     // Stores only and out to the point of unification only
    |   'OSHST' |   'oshst'     // Stores only and outer sharable domain only
    |   'ISH'   |   'ish'       // Inner sharable domain only
    |   'NSH'   |   'nsh'       // Out to the point of unification only
    |   'OSH'   |   'osh'       // Outer sharable domain only
    ;

// Bracnch conditions

EQ  :   'EQ';    // Equal
NE  :   'NE';    // Not equal
CS  :   'CS';    // Carry set
HS  :   'HS';    // Identical to CS
CC  :   'CC';    // Carry clear
LO  :   'LO';    // Identical to CC
MI  :   'MI';	 // Minus or negative result
PL  :   'PL';    // Positive or zero result
VS  :   'VS';    // Overflow
VC  :   'VC';    // No overflow
HI  :   'HI';    // Unsigned higher
LS  :   'LS';    // Unsigned lower or same
GE  :   'GE';    // Signed greater than or equal
LT  :   'LT';    // Signed less than
GT  :   'GT';    // Signed greater than
LE  :   'LE';    // Signed less than or equal
AL  :   'AL';    // Always (this is the default)

// Branch conditions shortcut instructions

CBZ     :   'CBZ';      // Branch if zero
CBNZ    :   'CBNZ';     // Branch if not zero

// Shift operators

LSL :   'LSL';   // Logical shift left
LSR :   'LSR';   // Logical shift right
ASR :   'ASR';   // Arithmetic shift right (preserves sign bit)

BitfieldOperator
    :   'UXTW' // Zero extends a 32-bit word (unsigned)
    |   'SXTW' // Zero extends a 32-bit word (signed)
    ;

Register64
    :   'X' DigitSequence
    ;

Register32
    :   'W' DigitSequence
    ;

LitmusLanguage
    :   'AArch64'
    ;