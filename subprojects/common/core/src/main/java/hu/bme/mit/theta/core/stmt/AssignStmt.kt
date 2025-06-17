package hu.bme.mit.theta.core.stmt

import hu.bme.mit.theta.common.Utils
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

/**
 * Assignment statement of the form `VARIABLE := EXPRESSION`. The statement updates the VARIABLE with
 * the result of EXPRESSION.
 *
 * @param <DeclType>
 */
@Serializable
@SerialName(AssignStmt.STMT_LABEL)
data class AssignStmt<DeclType : Type>(
    val varDecl: VarDecl<DeclType>,
    val expr: Expr<DeclType>
) : Stmt {

    companion object {

        internal const val STMT_LABEL = "assign"

        @JvmStatic
        fun <DeclType : Type> of(lhs: VarDecl<DeclType>, rhs: Expr<DeclType>): AssignStmt<DeclType> =
            AssignStmt(lhs, rhs)

        @JvmStatic
        @Suppress("UNCHECKED_CAST")
        fun <DeclType : Type> create(lhs: VarDecl<*>, rhs: Expr<*>): AssignStmt<DeclType> {
            val newLhs = lhs as VarDecl<DeclType>
            val newRhs = cast(rhs, newLhs.type)
            return of(newLhs, newRhs)
        }
    }

    override fun <P, R> accept(visitor: StmtVisitor<P, R>, param: P): R = visitor.visit(this, param)

    override fun toString(): String = Utils.lispStringBuilder(STMT_LABEL).add(varDecl.name).add(expr).toString()
}
