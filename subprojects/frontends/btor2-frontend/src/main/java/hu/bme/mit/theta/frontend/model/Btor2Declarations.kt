import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.bvtype.BvType
import hu.bme.mit.theta.frontend.model.Btor2Node
import hu.bme.mit.theta.frontend.model.Btor2NodeVisitor
import java.math.BigInteger

// Declarations

// TODO needs to be generalized if arrays are added
abstract class Btor2Sort(override val nid: UInt, open val width: UInt) : Btor2Node(nid) {
    abstract fun getType() : BvType
}

// TODO start supporting arrays
// data class Btor2ArrayDeclaration(val id: Int, val indexSort: Btor2SortDeclaration, val elementSort: Btor2SortDeclaration)
data class Btor2BvSort(override val nid: UInt, override val width: UInt) : Btor2Sort(nid, width) {
    override fun getType(): BvType {
        return BvType.of(width.toInt())
    }

    override fun <R, P> accept(visitor: Btor2NodeVisitor<R, P>, param : P): R {
        return visitor.visit(this, param)
    }
}

// Constants
// it can be in binary, decimal or hex in the circuit, but we extract the actual value to the int from that
data class Btor2Const(override val nid: UInt, val value: BigInteger, override val sort: Btor2Sort) : Btor2Node(nid) {
    private val constVar = Var("node_" + nid, sort.getType())
    override fun <R, P> accept(visitor: Btor2NodeVisitor<R, P>, param : P): R {
        return visitor.visit(this, param)
    }

    fun getVar(): VarDecl<BvType> {
        return constVar
    }
}