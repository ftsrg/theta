package hu.bme.mit.theta.core.type.arraytype

import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.NeqExpr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

/**
 * Not-equal expression for array types.
 */
@Serializable
@SerialName("ArrayNeqExpr")
data class ArrayNeqExpr<IndexType : Type, ElemType : Type>(
    override val leftOp: Expr<ArrayType<IndexType, ElemType>>,
    override val rightOp: Expr<ArrayType<IndexType, ElemType>>
) : NeqExpr<ArrayType<IndexType, ElemType>>() {

    companion object {
        @JvmStatic
        fun <IndexType : Type, ElemType : Type> of(
            leftOp: Expr<ArrayType<IndexType, ElemType>>,
            rightOp: Expr<ArrayType<IndexType, ElemType>>
        ) = ArrayNeqExpr(leftOp, rightOp)
        @JvmStatic
        fun <IndexType : Type, ElemType : Type> create(
            leftOp: Expr<*>, rightOp: Expr<*>
        ): ArrayNeqExpr<*, *> {
            @Suppress("UNCHECKED_CAST")
            val arrayType = leftOp.type as ArrayType<IndexType, ElemType>
            val newLeftOp = cast(leftOp, arrayType)
            val newRightOp = cast(rightOp, arrayType)
            return of(newLeftOp, newRightOp)
        }
    }

    override fun eval(`val`: Valuation): LitExpr<BoolType> = throw UnsupportedOperationException()

    override fun of(
        leftOp: Expr<ArrayType<IndexType, ElemType>>,
        rightOp: Expr<ArrayType<IndexType, ElemType>>
    ): ArrayNeqExpr<IndexType, ElemType> =
        Companion.of(leftOp, rightOp)

    override fun toString(): String = super.toString()
}
