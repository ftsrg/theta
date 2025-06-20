package hu.bme.mit.theta.core.type.arraytype

import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import kotlinx.serialization.Serializable

/**
 * Factory and utility methods for array-type expressions.
 */
object ArrayExprs {
    @JvmStatic
    fun <IndexType : Type, ElemType : Type> Array(
        indexType: IndexType,
        elemType: ElemType
    ): ArrayType<IndexType, ElemType> =
        ArrayType(indexType, elemType)

    @JvmStatic
    fun <IndexType : Type, ElemType : Type> Array(
        elements: List<Pair<Expr<IndexType>, Expr<ElemType>>>,
        elseElem: Expr<ElemType>,
        type: ArrayType<IndexType, ElemType>
    ): ArrayLitExpr<IndexType, ElemType> =
        ArrayLitExpr.of(elements, elseElem, type)

    @JvmStatic
    fun <IndexType : Type, ElemType : Type> ArrayInit(
        elements: List<Pair<Expr<IndexType>, Expr<ElemType>>>,
        elseElem: Expr<ElemType>,
        type: ArrayType<IndexType, ElemType>
    ): ArrayInitExpr<IndexType, ElemType> =
        ArrayInitExpr(elements, elseElem, type)

    @JvmStatic
    fun <IndexType : Type, ElemType : Type> Read(
        array: Expr<ArrayType<IndexType, ElemType>>,
        index: Expr<IndexType>
    ): ArrayReadExpr<IndexType, ElemType> =
        ArrayReadExpr(array, index)

    @JvmStatic
    fun <IndexType : Type, ElemType : Type> Write(
        array: Expr<ArrayType<IndexType, ElemType>>,
        index: Expr<IndexType>,
        elem: Expr<ElemType>
    ): ArrayWriteExpr<IndexType, ElemType> =
        ArrayWriteExpr(array, index, elem)

    @JvmStatic
    fun <IndexType : Type, ElemType : Type> Eq(
        leftOp: Expr<ArrayType<IndexType, ElemType>>,
        rightOp: Expr<ArrayType<IndexType, ElemType>>
    ): ArrayEqExpr<IndexType, ElemType> =
        ArrayEqExpr(leftOp, rightOp)

    @JvmStatic
    fun <IndexType : Type, ElemType : Type> Neq(
        leftOp: Expr<ArrayType<IndexType, ElemType>>,
        rightOp: Expr<ArrayType<IndexType, ElemType>>
    ): ArrayNeqExpr<IndexType, ElemType> =
        ArrayNeqExpr(leftOp, rightOp)
}
