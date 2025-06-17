package hu.bme.mit.theta.core.stmt

import hu.bme.mit.theta.common.Utils
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolType
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

/**
 * If-then-else statement of the form `if (COND) THEN [else ELSE]`. The statement first evaluates
 * the condition COND, and based on its value, executes either the THEN or the ELSE branch.
 * The ELSE branch is optional and defaults to a skip statement.
 */
@Serializable
@SerialName(IfStmt.STMT_LABEL)
data class IfStmt(
    val cond: Expr<BoolType>,
    val then: Stmt,
    val elze: Stmt
) : Stmt {

    companion object {
        internal const val STMT_LABEL = "if"

        @JvmStatic
        fun of(cond: Expr<BoolType>, then: Stmt, elze: Stmt): IfStmt = IfStmt(cond, then, elze)

        @JvmStatic
        fun of(cond: Expr<BoolType>, then: Stmt): IfStmt = IfStmt(cond, then, SkipStmt)
    }

    override fun <P, R> accept(visitor: StmtVisitor<P, R>, param: P): R = visitor.visit(this, param)

    override fun toString(): String = Utils.lispStringBuilder(STMT_LABEL).add(cond).add(then).add(elze).toString()
}
