package hu.bme.mit.theta.core.stmt

import hu.bme.mit.theta.common.Utils
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.anytype.Dereference
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

/**
 * Assignment statement of the form `*(DEREF_EXPRESSION) := EXPRESSION`. The statement updates the
 * value pointed to by DEREF_EXPRESSION with the result of EXPRESSION.
 *
 * @param PtrType The type of the pointer
 * @param OffsetType The type of the offset
 * @param DeclType The type of the value being assigned
 */
@Serializable
@SerialName(MemoryAssignStmt.STMT_LABEL)
data class MemoryAssignStmt<PtrType : Type, OffsetType : Type, DeclType : Type>(
    val deref: Dereference<PtrType, OffsetType, DeclType>,
    val expr: Expr<DeclType>
) : Stmt {

    companion object {

        internal const val STMT_LABEL = "memassign"

        @JvmStatic
        fun <PtrType : Type, OffsetType : Type, DeclType : Type> of(
            deref: Dereference<PtrType, OffsetType, DeclType>,
            expr: Expr<DeclType>
        ): MemoryAssignStmt<PtrType, OffsetType, DeclType> = MemoryAssignStmt(deref, expr)

        @JvmStatic
        @Suppress("UNCHECKED_CAST")
        fun <PtrType : Type, OffsetType : Type, DeclType : Type> create(
            deref: Dereference<PtrType, OffsetType, *>,
            expr: Expr<DeclType>
        ): MemoryAssignStmt<PtrType, OffsetType, DeclType> {
            val typedDeref = deref as Dereference<PtrType, OffsetType, DeclType>
            return of(typedDeref, expr)
        }
    }

    override fun <P, R> accept(visitor: StmtVisitor<P, R>, param: P): R =
        visitor.visit(this, param)

    override fun toString(): String =
        Utils.lispStringBuilder(STMT_LABEL).add(deref).add(expr).toString()
}
