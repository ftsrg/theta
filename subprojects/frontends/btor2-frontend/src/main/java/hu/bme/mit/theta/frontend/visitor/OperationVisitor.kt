package hu.bme.mit.theta.frontend.visitor

import Btor2BvSort
import Btor2Sort
import hu.bme.mit.theta.btor2.frontend.dsl.gen.Btor2BaseVisitor
import hu.bme.mit.theta.btor2.frontend.dsl.gen.Btor2Parser
import hu.bme.mit.theta.frontend.model.*
import jdk.jshell.spi.ExecutionControl.NotImplementedException

class OperationVisitor(private val idVisitor : IdVisitor, private val sorts : Map<UInt, Btor2Sort>, private val nodes : Map<UInt, Btor2Node>) : Btor2BaseVisitor<Btor2Node>() {
    override fun visitOperation(ctx: Btor2Parser.OperationContext): Btor2Node {
        check(ctx.childCount==1)
        return ctx.children[0].accept(this)
    }

    override fun visitExt(ctx: Btor2Parser.ExtContext): Btor2Node {
        val nid = idVisitor.visit(ctx.id)
        val sid = idVisitor.visit(ctx.sid())
        val sort : Btor2BvSort = sorts[sid] as Btor2BvSort

        val opd = nodes[ctx.opd1.text.toUInt()] as Btor2Node
        val w = ctx.w.text.toUInt()

        check(sort.width == (opd.sort as Btor2BvSort).width + w)

        return Btor2ExtOperation(nid, sort, opd, w)
    }

    override fun visitSlice(ctx: Btor2Parser.SliceContext): Btor2Node {
        val nid = idVisitor.visit(ctx.id)
        val sid = idVisitor.visit(ctx.sid())
        val sort : Btor2BvSort = sorts[sid] as Btor2BvSort

        val opd = nodes[ctx.opd1.text.toUInt()] as Btor2Node
        val u = ctx.u.text.toUInt()
        val l = ctx.l.text.toUInt()

        return Btor2SliceOperation(nid, sort, opd, u, l)
    }

    override fun visitUnop(ctx: Btor2Parser.UnopContext): Btor2Node {
        val nid = idVisitor.visit(ctx.id)
        val sid = idVisitor.visit(ctx.sid())
        val sort : Btor2BvSort = sorts[sid] as Btor2BvSort

        val op = when (ctx.UNARYOP().text) {
            "not" -> Btor2UnaryOperator.NOT
            "inc" -> Btor2UnaryOperator.INC
            "dec" -> Btor2UnaryOperator.DEC
            "neg" -> Btor2UnaryOperator.NEG
            "redand" -> Btor2UnaryOperator.REDAND
            "redor" -> Btor2UnaryOperator.REDOR
            "redxor" -> Btor2UnaryOperator.REDXOR
            else -> throw RuntimeException("Unary operator unknown")
        }

        val opd = nodes[ctx.opd1.text.toUInt()] as Btor2Node
        if (arrayOf(Btor2UnaryOperator.REDAND, Btor2UnaryOperator.REDOR, Btor2UnaryOperator.REDXOR).contains(op)) {
            check(sort.width == 1u)
        } else {
            check(sort.width == (opd.sort as Btor2BvSort).width)
        }

        return Btor2UnaryOperation(nid, sort, op, opd)
    }

    override fun visitBinop(ctx: Btor2Parser.BinopContext): Btor2Node {
        val nid = idVisitor.visit(ctx.id)
        val sid = idVisitor.visit(ctx.sid())
        val sort : Btor2BvSort = sorts[sid] as Btor2BvSort

        val opd1 = nodes[ctx.opd1.text.toUInt()] as Btor2Node
        val opd2 = nodes[ctx.opd2.text.toUInt()] as Btor2Node

        val op = when (ctx.BINOP().text) {
            "and" -> Btor2BinaryOperator.AND
            "nand" -> Btor2BinaryOperator.NAND
            "nor" -> Btor2BinaryOperator.NOR
            "or" -> Btor2BinaryOperator.OR
            "xor" -> Btor2BinaryOperator.XOR
            "iff" -> Btor2BinaryOperator.IFF
            "implies" -> Btor2BinaryOperator.IMPLIES
            "eq" -> Btor2BinaryOperator.EQ
            "neq" -> Btor2BinaryOperator.NEQ
            "slt" -> Btor2BinaryOperator.SLT
            "sle" -> Btor2BinaryOperator.SLE
            "sgt" -> Btor2BinaryOperator.SGT
            "sgte" -> Btor2BinaryOperator.SGTE
            "ult" -> Btor2BinaryOperator.ULT
            "ule" -> Btor2BinaryOperator.ULE
            "ugt" -> Btor2BinaryOperator.UGT
            "ugte" -> Btor2BinaryOperator.UGTE
            "concat" -> Btor2BinaryOperator.CONCAT
            "add" -> Btor2BinaryOperator.ADD
            "mul" -> Btor2BinaryOperator.MUL
            "udiv" -> Btor2BinaryOperator.UDIV
            "urem" -> Btor2BinaryOperator.UREM
            "sdiv" -> Btor2BinaryOperator.SDIV
            "srem" -> Btor2BinaryOperator.SREM
            "smod" -> Btor2BinaryOperator.SMOD
            "saddo" -> Btor2BinaryOperator.SADDO
            "sdivo" -> Btor2BinaryOperator.SDIVO
            "smulo" -> Btor2BinaryOperator.SMULO
            "ssubo" -> Btor2BinaryOperator.SSUBO
            "uaddo" -> Btor2BinaryOperator.UADDO
            "umulo" -> Btor2BinaryOperator.UMULO
            "usubo" -> Btor2BinaryOperator.USUBO
            "rol" -> Btor2BinaryOperator.ROL
            "ror" -> Btor2BinaryOperator.ROR
            "sll" -> Btor2BinaryOperator.SLL
            "sra" -> Btor2BinaryOperator.SRA
            "srl" -> Btor2BinaryOperator.SRL
            "read" -> Btor2BinaryOperator.READ
            else -> throw RuntimeException("Unary operator unknown")
        }

        // some type checks, just to make sure - although we DO expect the user to check their circuit with catbtor first
        if (op == Btor2BinaryOperator.READ) {
            throw NotImplementedException("Array types not yet supported")
        } else if (OnexOnexOneBinOps.contains(op)) {
            check(sort.width == 1u)
            check((opd1.sort as Btor2BvSort).width == (opd2.sort as Btor2BvSort).width)
            check((opd1.sort as Btor2BvSort).width == sort.width)
        } else if (NxNxNBinOps.contains(op)) {
            check((opd1.sort as Btor2BvSort).width == (opd2.sort as Btor2BvSort).width)
            check((opd1.sort as Btor2BvSort).width == sort.width)
        } else if (NxNxOneBinOps.contains(op)) {
            check(sort.width==1u)
            check((opd1.sort as Btor2BvSort).width == (opd2.sort as Btor2BvSort).width)
        } else if (SxSxOneBinOps.contains(op)) {
            check(sort.width==1u)
            check((opd1.sort as Btor2BvSort).width == (opd2.sort as Btor2BvSort).width) // TODO change if array support added
        } else if (op == Btor2BinaryOperator.CONCAT) {
            check(sort.width == ((opd1.sort as Btor2BvSort).width + (opd2.sort as Btor2BvSort).width))
        }

        return Btor2BinaryOperation(nid, sort, op, opd1, opd2)
    }

    override fun visitTerop(ctx: Btor2Parser.TeropContext): Btor2Node {
        val nid = idVisitor.visit(ctx.id)
        val sid = idVisitor.visit(ctx.sid())
        val sort : Btor2BvSort = sorts[sid] as Btor2BvSort

        val op = when (ctx.TERNARYOP().text) {
            "ite" -> Btor2TernaryOperator.ITE
            "write" -> Btor2TernaryOperator.WRITE
            else -> throw RuntimeException("Ternary operator unknown")
        }

        val opd1 = nodes[ctx.opd1.text.toUInt()] as Btor2Node
        val opd2 = nodes[ctx.opd2.text.toUInt()] as Btor2Node
        val opd3 = nodes[ctx.opd3.text.toUInt()] as Btor2Node

        if (op == Btor2TernaryOperator.WRITE) {
            throw NotImplementedException("Array types not yet supported")
        } else {
            check((opd1.sort as Btor2BvSort).width == 1u)
            check((opd2.sort as Btor2BvSort).width == (opd3.sort as Btor2BvSort).width)
            check((opd3.sort as Btor2BvSort).width == sort.width)
        }

        return Btor2TernaryOperation(nid, sort, op, opd1, opd2, opd3)
    }

}

private val SxSxOneBinOps = arrayListOf(
    Btor2BinaryOperator.EQ,
    Btor2BinaryOperator.NEQ,
)

private val NxNxNBinOps = arrayListOf(
    Btor2BinaryOperator.AND,
    Btor2BinaryOperator.NAND,
    Btor2BinaryOperator.OR,
    Btor2BinaryOperator.NOR,
    Btor2BinaryOperator.XOR,
    Btor2BinaryOperator.XNOR,
    Btor2BinaryOperator.ROL,
    Btor2BinaryOperator.ROR,
    Btor2BinaryOperator.SLL,
    Btor2BinaryOperator.NOR,
    Btor2BinaryOperator.SRA,
    Btor2BinaryOperator.SRL,
    Btor2BinaryOperator.ADD,
    Btor2BinaryOperator.MUL,
    Btor2BinaryOperator.SDIV,
    Btor2BinaryOperator.UDIV,
    Btor2BinaryOperator.SMOD,
    Btor2BinaryOperator.SREM,
    Btor2BinaryOperator.UREM,
    Btor2BinaryOperator.SUB,
)

private val OnexOnexOneBinOps = arrayListOf(
    Btor2BinaryOperator.IFF,
    Btor2BinaryOperator.IMPLIES,
)

private val NxNxOneBinOps = arrayListOf(
    Btor2BinaryOperator.SGT,
    Btor2BinaryOperator.UGT,
    Btor2BinaryOperator.SGTE,
    Btor2BinaryOperator.UGTE,
    Btor2BinaryOperator.SLT,
    Btor2BinaryOperator.ULT,
    Btor2BinaryOperator.SLTE,
    Btor2BinaryOperator.ULTE,
    Btor2BinaryOperator.SADDO,
    Btor2BinaryOperator.UADDO,
    Btor2BinaryOperator.SDIVO,
    Btor2BinaryOperator.SMULO,
    Btor2BinaryOperator.UMULO,
    Btor2BinaryOperator.SSUBO,
    Btor2BinaryOperator.USUBO,
)