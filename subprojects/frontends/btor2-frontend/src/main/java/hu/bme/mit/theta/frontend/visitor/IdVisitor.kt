package hu.bme.mit.theta.frontend.visitor

import hu.bme.mit.theta.btor2.frontend.dsl.gen.Btor2BaseVisitor
import hu.bme.mit.theta.btor2.frontend.dsl.gen.Btor2Parser

class IdVisitor : Btor2BaseVisitor<UInt>() {
    override fun visitNid(ctx: Btor2Parser.NidContext): UInt {
        val nid = ctx.NUM().text.toUInt()
        if (nid == 0u) {
            throw RuntimeException("nid should be bigger than 0")
        }
        return nid
    }

    override fun visitSid(ctx: Btor2Parser.SidContext): UInt {
        val sid = ctx.NUM().text.toUInt()
        if (sid == 0u) {
            throw RuntimeException("nid should be bigger than 0")
        }
        return sid
    }

}