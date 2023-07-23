package hu.bme.mit.theta.frontend.model

import Btor2Const
import Btor2Sort

// Inputs and States
data class Btor2Input(override val nid: UInt, override val sort: Btor2Sort) : Btor2Node(nid)
data class Btor2State(override val nid: UInt, override val sort: Btor2Sort) : Btor2Node(nid)
data class Btor2Init(override val nid: UInt, override val sort: Btor2Sort, val state: Btor2State, val value: Btor2Const) : Btor2Node(nid)
data class Btor2Next(override val nid: UInt, override val sort: Btor2Sort, val state: Btor2State, val value: Btor2Node) : Btor2Node(nid)

// Property Nodes
// data class Btor2JusticeNode(val id: Int, val num: Int, val children: List<Btor2Node>) : Btor2Node(id)
data class Btor2Bad(override val nid: UInt, val operand: Btor2Node) : Btor2Node(nid)
data class Btor2Constraint(override val nid: UInt, val operand: Btor2Node) : Btor2Node(nid)
data class Btor2Output(override val nid: UInt, val operand: Btor2Node) : Btor2Node(nid)
