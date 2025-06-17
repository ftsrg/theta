package hu.bme.mit.theta.core.stmt

import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

@Serializable
@SerialName(SkipStmt.STMT_LABEL)
data object SkipStmt : Stmt {
    internal const val STMT_LABEL = "skip"

    override fun <P, R> accept(visitor: StmtVisitor<in P, out R>, param: P): R {
        return visitor.visit(this, param)
    }
    
    override fun toString(): String = STMT_LABEL
}
