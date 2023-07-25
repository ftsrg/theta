package hu.bme.mit.theta.frontend.visitor

import Btor2BvSort
import Btor2Const
import Btor2Sort
import hu.bme.mit.theta.btor2.frontend.dsl.gen.Btor2BaseVisitor
import hu.bme.mit.theta.btor2.frontend.dsl.gen.Btor2Parser
import hu.bme.mit.theta.frontend.model.*

class StatefulVisitor(private val idVisitor : IdVisitor, private val sorts : Map<UInt, Btor2Sort>, private val nodes : Map<UInt, Btor2Node>) : Btor2BaseVisitor<Btor2Node>() {
    override fun visitStateful(ctx: Btor2Parser.StatefulContext): Btor2Node {
        check(ctx.childCount==1)
        return ctx.children[0].accept(this)
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

}