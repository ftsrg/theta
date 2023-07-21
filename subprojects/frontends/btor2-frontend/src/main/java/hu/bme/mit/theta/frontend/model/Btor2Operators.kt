package hu.bme.mit.theta.frontend.model

import Btor2BvSortDeclaration
import Btor2ConstDeclaration
import Btor2StateDeclaration

// Operator Nodes
data class Btor2InitNode(val id: Int, val nodeType: Btor2BvSortDeclaration, val sortId: Btor2BvSortDeclaration, val state: Btor2StateDeclaration, val value: Btor2ConstDeclaration) : Btor2Node(id)
data class Btor2NextNode(val id: Int, val nodeType: Btor2BvSortDeclaration, val sortId: Btor2BvSortDeclaration, val state: Btor2StateDeclaration, val value: Btor2Node) : Btor2Node(id)
// TODO support justice nodes...? (not reachability, but an invariant)
// data class Btor2JusticeNode(val id: Int, val num: Int, val children: List<Btor2Node>) : Btor2Node(id)
data class Btor2BadNode(val id: Int, val operand: Btor2Node) : Btor2Node(id)

// Operators
data class Btor2UnaryOperation(val nodeId: Int, val operator: Btor2UnaryOperator, val operand: Btor2Node) : Btor2Node(nodeId)
data class Btor2BinaryOperation(val nodeId: Int, val operator: Btor2BinaryOperator, val operand1: Btor2Node, val operand2: Btor2Node) : Btor2Node(nodeId)
data class Btor2TernaryOperation(val nodeId: Int, val operator: Btor2TernaryOperator, val condition: Btor2Node, val trueValue: Btor2Node, val falseValue: Btor2Node) : Btor2Node(nodeId)
enum class Btor2UnaryOperator {
    NOT,
    INC,
    DEC,
    NEG,
    REDAND,
    REDOR,
    REDXOR
}

enum class Btor2BinaryOperator {
    IFF,
    IMPLIES,
    EQ,
    NEQ,
    SGT,
    SGTE,
    SLT,
    SLTE,
    UGT,
    UGTE,
    ULT,
    ULTE,
    AND,
    NAND,
    NOR,
    OR,
    XNOR,
    XOR,
    ROL,
    ROR,
    SLL,
    SRA,
    SRL,
    ADD,
    MUL,
    SDIV,
    SREM,
    SMOD,
    UDIV,
    UREM,
    UMOD,
    SUB
}

enum class Btor2TernaryOperator {
    ITE,
    WRITE
}
