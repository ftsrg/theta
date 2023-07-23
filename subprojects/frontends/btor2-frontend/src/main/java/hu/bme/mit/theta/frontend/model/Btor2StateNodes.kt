package hu.bme.mit.theta.frontend.model

import Btor2BvSort
import Btor2Const
import Btor2Sort
import Btor2State

class Btor2StateNodes {
    // Operator Nodes
    data class Btor2InitNode(override val nid: UInt, override val sort: Btor2Sort, val state: Btor2State, val value: Btor2Const) : Btor2Node(nid)
    data class Btor2NextNode(override val nid: UInt, override val sort: Btor2Sort, val state: Btor2State, val value: Btor2Node) : Btor2Node(nid)

    // data class Btor2JusticeNode(val id: Int, val num: Int, val children: List<Btor2Node>) : Btor2Node(id)
    data class Btor2BadNode(override val nid: UInt, val operand: Btor2Node) : Btor2Node(nid)
}