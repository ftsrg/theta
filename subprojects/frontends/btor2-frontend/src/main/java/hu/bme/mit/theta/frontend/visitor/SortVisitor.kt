package hu.bme.mit.theta.frontend.visitor

import Btor2BvSort
import Btor2Sort
import hu.bme.mit.theta.btor2.frontend.dsl.gen.Btor2BaseVisitor
import hu.bme.mit.theta.btor2.frontend.dsl.gen.Btor2Parser

class SortVisitor(val idVisitor: IdVisitor) : Btor2BaseVisitor<Btor2Sort>() {
    override fun visitSort(ctx: Btor2Parser.SortContext): Btor2Sort {
        check(ctx.childCount==1)
        return ctx.children[0].accept(this)
    }

    override fun visitArray_sort(ctx: Btor2Parser.Array_sortContext): Btor2Sort {
        throw NotImplementedError()
    }

    override fun visitBitvec_sort(ctx: Btor2Parser.Bitvec_sortContext): Btor2Sort {
        val sid = idVisitor.visit(ctx.id)
        val width = ctx.width.text.toUInt()
        if(width <= 0u) {
            throw RuntimeException("Bitvector width should be bigger than 0")
        }
        return Btor2BvSort(sid, width)
    }
}