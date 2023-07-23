package hu.bme.mit.theta.frontend.visitor

import hu.bme.mit.theta.btor2.frontend.dsl.gen.Btor2BaseVisitor
import hu.bme.mit.theta.btor2.frontend.dsl.gen.Btor2Parser

class IdVisitor : Btor2BaseVisitor<Int>() {
    override fun visitNid(ctx: Btor2Parser.NidContext): Int {
        val nid = ctx.NUM().text.toInt()
        if (nid <= 0) {
            throw RuntimeException("nid should be bigger than 0")
        }
        return nid
    }

    override fun visitSid(ctx: Btor2Parser.SidContext): Int {
        val sid = ctx.NUM().text.toInt()
        if (sid <= 0) {
            throw RuntimeException("nid should be bigger than 0")
        }
        return sid
    }

}