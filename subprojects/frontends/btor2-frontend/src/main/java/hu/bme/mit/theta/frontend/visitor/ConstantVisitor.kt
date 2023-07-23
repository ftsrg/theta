package hu.bme.mit.theta.frontend.visitor

import Btor2BvSort
import Btor2Const
import Btor2Sort
import hu.bme.mit.theta.btor2.frontend.dsl.gen.Btor2BaseVisitor
import hu.bme.mit.theta.btor2.frontend.dsl.gen.Btor2Parser
import java.math.BigInteger

class ConstantVisitor(val idVisitor : IdVisitor, val sorts : Map<Int, Btor2Sort>) : Btor2BaseVisitor<Btor2Const>() {
    override fun visitConstantNode(ctx: Btor2Parser.ConstantNodeContext): Btor2Const {
        check(ctx.childCount==1)
        return ctx.children[0].accept(this)
    }

    override fun visitConstant(ctx: Btor2Parser.ConstantContext): Btor2Const {
        val nid = idVisitor.visit(ctx.nid())
        val sid = idVisitor.visit(ctx.sid())
        val sort : Btor2BvSort = sorts[sid] as Btor2BvSort

        val value = BigInteger(ctx.bin.text, 2)
        val node = Btor2Const(nid, value, sort)
        return node
    }

    override fun visitConstant_d(ctx: Btor2Parser.Constant_dContext): Btor2Const {
        val nid = idVisitor.visit(ctx.nid())
        val sid = idVisitor.visit(ctx.sid())
        val sort : Btor2BvSort = sorts[sid] as Btor2BvSort

        var value = BigInteger(ctx.dec.text)
        ctx.MINUS()?.let{ value = value.multiply(BigInteger("-1")) }
        val node = Btor2Const(nid, value, sort)
        return node
    }

    override fun visitConstant_h(ctx: Btor2Parser.Constant_hContext): Btor2Const {
        val nid = idVisitor.visit(ctx.nid())
        val sid = idVisitor.visit(ctx.sid())
        val sort : Btor2BvSort = sorts[sid] as Btor2BvSort

        val value = BigInteger(ctx.hex.text, 16)
        val node = Btor2Const(nid, value, sort)
        return node
    }
}