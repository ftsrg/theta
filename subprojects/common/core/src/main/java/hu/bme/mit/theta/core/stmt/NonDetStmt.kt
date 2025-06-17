package hu.bme.mit.theta.core.stmt

import hu.bme.mit.theta.common.Utils
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

/**
 * Non-deterministic statement of the form `nondet { STMT1, STMT2, ... }`. The statement executes
 * exactly one of the given statements, chosen non-deterministically.
 */
@Serializable
@SerialName(NonDetStmt.STMT_LABEL)
data class NonDetStmt(
    val stmts: List<Stmt>
) : Stmt {

    init {
        check(stmts.isNotEmpty())
    }

    companion object {

        internal const val STMT_LABEL = "nondet"

        @JvmStatic
        fun of(stmts: List<Stmt>): NonDetStmt {
            val stmtList = stmts.ifEmpty {
                listOf(SkipStmt)
            }
            return NonDetStmt(stmtList)
        }
    }

    override fun <P, R> accept(visitor: StmtVisitor<P, R>, param: P): R =
        visitor.visit(this, param)

    override fun toString(): String = Utils.lispStringBuilder(STMT_LABEL).addAll(stmts).toString()
}
