package hu.bme.mit.theta.frontend.visitor

import Btor2BvSort
import Btor2Const
import Btor2Sort
import hu.bme.mit.theta.btor2.frontend.dsl.gen.Btor2BaseVisitor
import hu.bme.mit.theta.btor2.frontend.dsl.gen.Btor2Parser
import hu.bme.mit.theta.frontend.model.*
import kotlin.collections.LinkedHashMap

class Btor2Visitor : Btor2BaseVisitor<Btor2Node>() {
    val sorts = LinkedHashMap<UInt, Btor2Sort>()
    val nodes = LinkedHashMap<UInt, Btor2Node>()
    private val idVisitor = IdVisitor()
    private val sortVisitor = SortVisitor(idVisitor)
    private val constantVisitor = ConstantVisitor(idVisitor, sorts)
    private val operationVisitor = OperationVisitor(idVisitor, sorts, nodes)

    override fun visitSort(ctx: Btor2Parser.SortContext): Btor2Node {
        val newSort = sortVisitor.visit(ctx)
        check(!sorts.containsKey(newSort.nid))
        sorts[newSort.nid] = newSort
        return newSort
    }

    override fun visitConstantNode(ctx: Btor2Parser.ConstantNodeContext): Btor2Node {
        val newConstant = constantVisitor.visit(ctx)
        check(!nodes.containsKey(newConstant.nid))
        nodes[newConstant.nid] = newConstant
        return newConstant
    }

    override fun visitOperation(ctx: Btor2Parser.OperationContext): Btor2Node {
        val opNode = operationVisitor.visit(ctx)
        check(!nodes.containsKey(opNode.nid))
        nodes[opNode.nid] = opNode
        return opNode
    }

    override fun visitStateful(ctx: Btor2Parser.StatefulContext?): Btor2Node {
        val node = visit(ctx)
        nodes[node.nid] = node
        return node
    }

    override fun visitInput(ctx: Btor2Parser.InputContext): Btor2Node {
        val nid = idVisitor.visit(ctx.id)
        val sid = idVisitor.visit(ctx.sid())
        val sort = sorts[sid] as Btor2Sort

        return Btor2Input(nid, sort)
    }

    override fun visitInit(ctx: Btor2Parser.InitContext): Btor2Node {
        val nid = idVisitor.visit(ctx.id)
        val sid = idVisitor.visit(ctx.sid())
        val sort = sorts[sid] as Btor2Sort

        val param1 = nodes[ctx.param1.NUM().text.toUInt()] as Btor2State
        val param2 = nodes[ctx.param2.NUM().text.toUInt()] as Btor2Const

        check((param1.sort as Btor2BvSort).width == (param2.sort as Btor2BvSort).width)

        return Btor2Init(nid, sort, param1, param2)
    }

    override fun visitNext(ctx: Btor2Parser.NextContext): Btor2Node {
        val nid = idVisitor.visit(ctx.id)
        val sid = idVisitor.visit(ctx.sid())
        val sort = sorts[sid] as Btor2Sort

        val param1 = nodes[ctx.param1.NUM().text.toUInt()] as Btor2State
        val param2 = nodes[ctx.param2.NUM().text.toUInt()] as Btor2Node

        return Btor2Next(nid, sort, param1, param2)
    }

    override fun visitState(ctx: Btor2Parser.StateContext): Btor2Node {
        val nid = idVisitor.visit(ctx.id)
        val sid = idVisitor.visit(ctx.sid())
        val sort = sorts[sid] as Btor2Sort

        return Btor2State(nid, sort)
    }

    override fun visitProperty(ctx: Btor2Parser.PropertyContext): Btor2Node {
        val nid = idVisitor.visit(ctx.id)
        val node : Btor2Node = when (ctx.property_type.text) {
            "bad" -> {
                Btor2Bad(nid, nodes[ctx.param.NUM().text.toUInt()] as Btor2Node)
            }
            "constraint" -> {
                Btor2Constraint(nid, nodes[ctx.param.NUM().text.toUInt()] as Btor2Node)
            }
            "output" -> { Btor2Output(nid, nodes[ctx.param.NUM().text.toUInt()] as Btor2Node) }
            "fair" -> { throw NotImplementedError() }
            "justice" -> { throw NotImplementedError() }
            else -> { throw RuntimeException("Property type unknown") }
        }
        return node
    }

    // TODO don't skip, add as metadata?
    // override fun visitSymbol(ctx: Btor2Parser.SymbolContext): Btor2Node {}
}
