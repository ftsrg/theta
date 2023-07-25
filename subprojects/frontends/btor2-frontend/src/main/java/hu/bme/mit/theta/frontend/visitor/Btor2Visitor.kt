package hu.bme.mit.theta.frontend.visitor

import Btor2BvSort
import Btor2Const
import Btor2Sort
import hu.bme.mit.theta.btor2.frontend.dsl.gen.Btor2BaseVisitor
import hu.bme.mit.theta.btor2.frontend.dsl.gen.Btor2Parser
import hu.bme.mit.theta.frontend.model.*
import kotlin.collections.LinkedHashMap

class Btor2Visitor() : Btor2BaseVisitor<Btor2Node>() {
    val sorts = LinkedHashMap<UInt, Btor2Sort>()
    val nodes = LinkedHashMap<UInt, Btor2Node>()
    private val idVisitor = IdVisitor()
    private val sortVisitor = SortVisitor(idVisitor)
    private val constantVisitor = ConstantVisitor(idVisitor, sorts)
    private val operationVisitor = OperationVisitor(idVisitor, sorts, nodes)
    private val statefulVisitor = StatefulVisitor(idVisitor, sorts, nodes)

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
        val Node = statefulVisitor.visit(ctx)
        check(!nodes.containsKey(Node.nid))
        nodes[Node.nid] = Node
        return Node
    }

    // TODO don't skip, add as metadata?
    // override fun visitSymbol(ctx: Btor2Parser.SymbolContext): Btor2Node {}
}
