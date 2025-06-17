package hu.bme.mit.theta.core.stmt

import hu.bme.mit.theta.common.Utils
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.inttype.IntType
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

/**
 * Loop statement of the form `for (LOOP_VAR = FROM to TO) { BODY }`. The statement executes the
 * BODY statement repeatedly, with LOOP_VAR taking on values from FROM to TO (inclusive).
 */
@Serializable
@SerialName(LoopStmt.STMT_LABEL)
data class LoopStmt(
    val stmt: Stmt,
    val loopVariable: VarDecl<IntType>,
    val from: Expr<IntType>,
    val to: Expr<IntType>
) : Stmt {

    companion object {
        internal const val STMT_LABEL = "loop"

        @JvmStatic
        fun of(
            stmt: Stmt,
            loopVar: VarDecl<IntType>,
            from: Expr<IntType>,
            to: Expr<IntType>
        ): LoopStmt = LoopStmt(stmt, loopVar, from, to)
    }

    override fun <P, R> accept(visitor: StmtVisitor<P, R>, param: P): R = visitor.visit(this, param)

    override fun toString(): String =
        Utils.lispStringBuilder(STMT_LABEL)
            .add("$loopVariable from $from to $to $stmt")
            .toString();
}
