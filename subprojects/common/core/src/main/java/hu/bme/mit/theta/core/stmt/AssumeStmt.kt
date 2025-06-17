package hu.bme.mit.theta.core.stmt

import hu.bme.mit.theta.common.Utils
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

/**
 * Assume statement of the form `[EXPRESSION]`, where EXPRESSION is a Boolean [Expr]. The
 * statement is a guard that can only be passed if EXPRESSION evaluates to true.
 */
@Serializable
@SerialName(AssumeStmt.STMT_LABEL)
data class AssumeStmt(val cond: Expr<BoolType>) : Stmt {

    companion object {

        internal const val STMT_LABEL = "assume"

        @JvmStatic
        fun of(cond: Expr<BoolType>): AssumeStmt = AssumeStmt(cond)

        @JvmStatic
        fun create(cond: Expr<BoolType>): AssumeStmt {
            val newCond = cast(cond, Bool())
            return of(newCond)
        }
    }

    override fun <P, R> accept(visitor: StmtVisitor<P, R>, param: P): R = visitor.visit(this, param)

    override fun toString(): String = Utils.lispStringBuilder(STMT_LABEL).add(cond).toString()
}
