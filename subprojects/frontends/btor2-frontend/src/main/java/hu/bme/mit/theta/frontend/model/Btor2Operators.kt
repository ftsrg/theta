package hu.bme.mit.theta.frontend.model

import Btor2Sort
import hu.bme.mit.theta.core.type.Expr

abstract class Btor2Operator(id: UInt) : Btor2Node(id)

// Operators
data class Btor2UnaryOperation(override val nid: UInt, override val sort : Btor2Sort, val operator: Btor2UnaryOperator, val operand: Btor2Node) : Btor2Operator(nid) {
    override fun <R, P> accept(visitor: Btor2NodeVisitor<R, P>, param : P): R {
        return visitor.visit(this, param)
    }
}
data class Btor2ExtOperation(override val nid: UInt, override val sort : Btor2Sort, val operand: Btor2Node, val w : UInt) : Btor2Operator(nid) {
    override fun <R, P> accept(visitor: Btor2NodeVisitor<R, P>, param : P): R {
        return visitor.visit(this, param)
    }
}
data class Btor2SliceOperation(override val nid: UInt, override val sort : Btor2Sort, val operand: Btor2Node, val u : UInt, val l : UInt) : Btor2Operator(nid) {
    override fun <R, P> accept(visitor: Btor2NodeVisitor<R, P>, param : P): R {
        return visitor.visit(this, param)
    }
}
data class Btor2BinaryOperation(override val nid: UInt, override val sort : Btor2Sort, val operator: Btor2BinaryOperator, val operand1: Btor2Node, val operand2: Btor2Node) : Btor2Operator(nid) {
    override fun <R, P> accept(visitor: Btor2NodeVisitor<R, P>, param : P): R {
        return visitor.visit(this, param)
    }
}
data class Btor2TernaryOperation(override val nid: UInt, override val sort : Btor2Sort, val operator: Btor2TernaryOperator, val condition: Btor2Node, val trueValue: Btor2Node, val falseValue: Btor2Node) : Btor2Operator(nid) {
    override fun <R, P> accept(visitor: Btor2NodeVisitor<R, P>, param : P): R {
        return visitor.visit(this, param)
    }
}
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
    SLE,
    SLTE,
    UGT,
    UGTE,
    ULT,
    ULE,
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
    SUB,
    CONCAT,
    SADDO,
    SDIVO,
    SMULO,
    SSUBO,
    UADDO,
    UMULO,
    USUBO,
    READ
}

enum class Btor2TernaryOperator {
    ITE,
    WRITE
}
