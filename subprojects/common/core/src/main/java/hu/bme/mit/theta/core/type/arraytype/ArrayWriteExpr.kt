package hu.bme.mit.theta.core.type.arraytype

import hu.bme.mit.theta.common.Utils
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

/**
 * Write expression for array types.
 */
@Serializable
@SerialName("ArrayWriteExpr")
data class ArrayWriteExpr<IndexType : Type, ElemType : Type>(
    val array: Expr<ArrayType<IndexType, ElemType>>,
    val index: Expr<IndexType>,
    val elem: Expr<ElemType>
) : Expr<ArrayType<IndexType, ElemType>> {

    companion object {

        private const val OPERATOR_LABEL = "write"

        fun <IndexType : Type, ElemType : Type> of(
            array: Expr<ArrayType<IndexType, ElemType>>,
            index: Expr<IndexType>,
            elem: Expr<ElemType>
        ) = ArrayWriteExpr(array, index, elem)

        @Suppress("UNCHECKED_CAST")
        fun <IndexType : Type, ElemType : Type> create(
            array: Expr<*>,
            index: Expr<*>,
            elem: Expr<*>
        ): ArrayWriteExpr<IndexType, ElemType> {
            val arrayType = array.type as ArrayType<IndexType, ElemType>
            val newArray = cast(array, arrayType)
            val newIndex = cast(index, arrayType.indexType)
            val newElem = cast(elem, arrayType.elemType)
            return of(newArray, newIndex, newElem)
        }
    }

    override val ops: List<Expr<*>> = listOf(array, index, elem)

    override val type: ArrayType<IndexType, ElemType> = ArrayType(index.type, elem.type)

    override fun eval(`val`: Valuation): LitExpr<ArrayType<IndexType, ElemType>> {
        val arrayVal = array.eval(`val`) as ArrayLitExpr<IndexType, ElemType>
        val indexVal = index.eval(`val`)
        val elemVal = elem.eval(`val`)
        val elemList = arrayVal.elements.filter { it.first != indexVal } + Pair(indexVal, elemVal)
        return ArrayLitExpr.of(elemList, arrayVal.elseElem, arrayVal.type)
    }

    override fun toString(): String =
        Utils.lispStringBuilder(OPERATOR_LABEL).body().add(array).add(index).add(elem).toString()

    override fun withOps(ops: List<Expr<*>>): ArrayWriteExpr<IndexType, ElemType> {
        require(ops.size == 3)
        val newArray = cast(ops[0], array.type)
        val newIndex = cast(ops[1], index.type)
        val newElem = cast(ops[2], elem.type)
        return with(newArray, newIndex, newElem)
    }

    fun with(
        array: Expr<ArrayType<IndexType, ElemType>>,
        index: Expr<IndexType>,
        elem: Expr<ElemType>
    ): ArrayWriteExpr<IndexType, ElemType> =
        if (this.array === array && this.index === index && this.elem === elem) {
            this
        } else {
            of(array, index, elem)
        }

    fun withIndex(index: Expr<IndexType>): ArrayWriteExpr<IndexType, ElemType> = with(array, index, elem)
    fun withElem(elem: Expr<ElemType>): ArrayWriteExpr<IndexType, ElemType> = with(array, index, elem)
}

