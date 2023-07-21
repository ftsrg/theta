import hu.bme.mit.theta.frontend.model.Btor2Node

// Declarations

// TODO start supporting arrays
//data class Btor2ArrayDeclaration(val id: Int, val indexSort: Btor2SortDeclaration, val elementSort: Btor2SortDeclaration)
data class Btor2BvSortDeclaration(val id: Int, val width: Int) : Btor2Node(id)

// Constants
data class Btor2ConstDeclaration(val id: Int, val value: Int, val type: Btor2BvSortDeclaration) : Btor2Node(id) // it can be in binary, decimal or hex in the circuit, but we extract the actual value to the int from that

// Inputs and States
data class Btor2InputDeclaration(val id: Int, val type: Btor2BvSortDeclaration) : Btor2Node(id)
data class Btor2StateDeclaration(val id: Int, val type: Btor2BvSortDeclaration) : Btor2Node(id)