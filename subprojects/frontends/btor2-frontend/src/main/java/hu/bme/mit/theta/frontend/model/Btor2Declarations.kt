import hu.bme.mit.theta.frontend.model.Btor2Node
import java.math.BigInteger

// Declarations

abstract class Btor2Sort(override val nid: UInt) : Btor2Node(nid)

// TODO start supporting arrays
// data class Btor2ArrayDeclaration(val id: Int, val indexSort: Btor2SortDeclaration, val elementSort: Btor2SortDeclaration)
data class Btor2BvSort(override val nid: UInt, val width: UInt) : Btor2Sort(nid)

// Constants
data class Btor2Const(override val nid: UInt, val value: BigInteger, val type: Btor2BvSort) : Btor2Node(nid) // it can be in binary, decimal or hex in the circuit, but we extract the actual value to the int from that