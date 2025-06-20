package hu.bme.mit.theta.core.type.arraytype

import hu.bme.mit.theta.common.Utils
import hu.bme.mit.theta.core.type.DomainSize
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.EqExpr
import hu.bme.mit.theta.core.type.abstracttype.Equational
import hu.bme.mit.theta.core.type.abstracttype.NeqExpr
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

/**
 * Represents an array type with a given index and element type.
 */
@Serializable
@SerialName(ArrayType.TYPE_LABEL)
data class ArrayType<IndexType : Type, ElemType : Type>(
    val indexType: IndexType,
    val elemType: ElemType
) : Equational<ArrayType<IndexType, ElemType>> {

    companion object {

        internal const val TYPE_LABEL = "Array"

        fun <IndexType : Type, ElemType : Type> of(
            indexType: IndexType, elemType: ElemType
        ): ArrayType<IndexType, ElemType> =
            ArrayType(indexType, elemType)
    }

    override fun Eq(
        leftOp: Expr<ArrayType<IndexType, ElemType>>,
        rightOp: Expr<ArrayType<IndexType, ElemType>>
    ): EqExpr<ArrayType<IndexType, ElemType>> = ArrayExprs.Eq(leftOp, rightOp)

    override fun Neq(
        leftOp: Expr<ArrayType<IndexType, ElemType>>,
        rightOp: Expr<ArrayType<IndexType, ElemType>>
    ): NeqExpr<ArrayType<IndexType, ElemType>> = ArrayExprs.Neq(leftOp, rightOp)

    override fun toString(): String =
        Utils.lispStringBuilder(TYPE_LABEL).add("([${indexType}] -> $elemType)").toString()

    override val domainSize: DomainSize
        get() = DomainSize.pow(elemType.domainSize, indexType.domainSize)
}

