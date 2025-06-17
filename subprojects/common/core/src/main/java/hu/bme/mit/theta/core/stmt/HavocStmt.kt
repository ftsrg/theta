package hu.bme.mit.theta.core.stmt

import hu.bme.mit.theta.common.Utils
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.decl.VarDecl
import kotlinx.serialization.Serializable
import kotlinx.serialization.SerialName

/**
 * Havoc statement of the form `havoc VARIABLE`, which performs a non-deterministic assignment to
 * VARIABLE.
 *
 * @param <DeclType>
 */
@Serializable
@SerialName(HavocStmt.STMT_LABEL)
data class HavocStmt<DeclType : Type>(
    val varDecl: VarDecl<DeclType>
) : Stmt {

    companion object {

        internal const val STMT_LABEL = "havoc"

        @JvmStatic
        fun <T : Type> of(varDecl: VarDecl<T>): HavocStmt<T> = HavocStmt(varDecl)
    }

    override fun <P, R> accept(visitor: StmtVisitor<P, R>, param: P): R = visitor.visit(this, param)

    override fun toString(): String = Utils.lispStringBuilder(STMT_LABEL).add(varDecl.name).toString()
}
