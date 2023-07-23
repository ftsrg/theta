package hu.bme.mit.theta.frontend.visitor

import Btor2Sort
import hu.bme.mit.theta.btor2.frontend.dsl.gen.Btor2BaseVisitor
import hu.bme.mit.theta.btor2.frontend.dsl.gen.Btor2Parser
import hu.bme.mit.theta.frontend.model.Btor2Node
import java.util.LinkedHashMap

class Btor2Visitor : Btor2BaseVisitor<Btor2Node>() {
    val idVisitor = IdVisitor()
    val sortVisitor = SortVisitor(idVisitor)
    val sorts = LinkedHashMap<Int, Btor2Sort>()
    val constantVisitor = ConstantVisitor(idVisitor, sorts)

    // Parser rules
    override fun visitBtor2(ctx: Btor2Parser.Btor2Context): Btor2Node {
        return visitChildren(ctx) // TODO
    }

    override fun visitLine(ctx: Btor2Parser.LineContext): Btor2Node {
        return visitChildren(ctx) // TODO
    }

    override fun visitSort(ctx: Btor2Parser.SortContext): Btor2Node {
        val newSort = sortVisitor.visit(ctx)
        check(!sorts.containsKey(newSort.nid))
        sorts[newSort.nid] = newSort
        return newSort
    }

    override fun visitConstantNode(ctx: Btor2Parser.ConstantNodeContext): Btor2Node {
        val newConstant = constantVisitor.visit(ctx)
        return newConstant
    }

    ////////////////////

    override fun visitInput(ctx: Btor2Parser.InputContext): Btor2Node {
        // Implementation for visiting input rule
        throw NotImplementedError()
    }

    override fun visitInit(ctx: Btor2Parser.InitContext): Btor2Node {
        // Implementation for visiting init rule
        throw NotImplementedError()
    }

    override fun visitNext(ctx: Btor2Parser.NextContext): Btor2Node {
        // Implementation for visiting next rule
        throw NotImplementedError()
    }

    override fun visitState(ctx: Btor2Parser.StateContext): Btor2Node {
        // Implementation for visiting state rule
        throw NotImplementedError()
    }

    override fun visitProperty(ctx: Btor2Parser.PropertyContext): Btor2Node {
        // Implementation for visiting property rule
        throw NotImplementedError()
    }

    override fun visitSymbol(ctx: Btor2Parser.SymbolContext): Btor2Node {
        // Implementation for visiting symbol rule
        throw NotImplementedError()
    }
}
