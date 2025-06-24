package hu.bme.mit.theta.core.stmt

import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

@Serializable
@SerialName(SkipStmt.STMT_LABEL)
data object SkipStmt : Stmt {

    internal const val STMT_LABEL = "skip"

    override fun <P, R> accept(visitor: StmtVisitor<P, R>, param: P): R =
        visitor.visit(this, param)

    @JvmStatic
    fun getInstance(): SkipStmt = this

    override fun toString(): String = STMT_LABEL
}
