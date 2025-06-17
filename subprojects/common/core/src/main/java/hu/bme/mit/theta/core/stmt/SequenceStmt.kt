package hu.bme.mit.theta.core.stmt

import hu.bme.mit.theta.common.Utils
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

/**
 * Sequence statement of the form `sequence { STMT1; STMT2; ... }`. The statement executes all of the
 * given statements in sequence.
 */
@Serializable
@SerialName(SequenceStmt.STMT_LABEL)
data class SequenceStmt(
    val stmts: List<Stmt>
) : Stmt {

    init {
        check(stmts.isNotEmpty())
    }

    companion object {

        internal const val STMT_LABEL = "sequence"

        @JvmStatic
        fun of(stmts: List<Stmt>): SequenceStmt {
            val stmtList = stmts.ifEmpty {
                listOf(SkipStmt)
            }
            return SequenceStmt(stmtList)
        }
    }

    override fun <P, R> accept(visitor: StmtVisitor<P, R>, param: P): R =
        visitor.visit(this, param)

    override fun toString(): String = Utils.lispStringBuilder().addAll(stmts).toString()
}
