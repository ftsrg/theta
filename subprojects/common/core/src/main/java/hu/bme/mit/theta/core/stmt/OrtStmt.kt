package hu.bme.mit.theta.core.stmt

import hu.bme.mit.theta.common.Utils
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

/**
 * Orthogonal statement of the form `ort { STMT1, STMT2, ... }`. The statement executes all of the
 * given statements in parallel.
 */
@Serializable
@SerialName(OrtStmt.STMT_LABEL)
data class OrtStmt(
    val stmts: List<Stmt>
) : Stmt {

    init {
        check(stmts.isNotEmpty())
    }

    companion object {

        internal const val STMT_LABEL = "ort"

        @JvmStatic
        fun of(stmts: List<Stmt>): OrtStmt {
            val stmtList = stmts.ifEmpty {
                listOf(SkipStmt)
            }
            return OrtStmt(stmtList)
        }
    }

    override fun <P, R> accept(visitor: StmtVisitor<P, R>, param: P): R =
        visitor.visit(this, param)

    override fun toString(): String = Utils.lispStringBuilder(STMT_LABEL).addAll(stmts).toString()
}
