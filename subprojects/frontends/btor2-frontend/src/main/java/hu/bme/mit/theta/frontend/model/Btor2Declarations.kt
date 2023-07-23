import hu.bme.mit.theta.frontend.model.Btor2Node
import java.math.BigInteger

// Declarations

abstract class Btor2Sort(open val sid : Int) : Btor2Node(sid)

// TODO start supporting arrays
// data class Btor2ArrayDeclaration(val id: Int, val indexSort: Btor2SortDeclaration, val elementSort: Btor2SortDeclaration)
data class Btor2BvSort(override val sid: Int, val width: Int) : Btor2Sort(sid)

// Constants
data class Btor2Const(override val nid: Int, val value: BigInteger, val type: Btor2BvSort) : Btor2Node(nid) // it can be in binary, decimal or hex in the circuit, but we extract the actual value to the int from that

// Inputs and States
data class Btor2Input(override val nid: Int, val type: Btor2BvSort) : Btor2Node(nid)
data class Btor2State(override val nid: Int, val type: Btor2BvSort) : Btor2Node(nid)