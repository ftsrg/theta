package hu.bme.mit.theta.core.type.arraytype

import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.MultiaryExpr
import hu.bme.mit.theta.core.type.Type
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

/**
 * ArrayInitExpr is a way to specify arbitrary array 'literals' that may contain non-literal
 * elements as well. Note that while this class is a descendant of MultiaryExpr, it is used in a
 * non-standard way: - ops is only used as a generic Type type, - ops are solely used for
 * inter-object interactions, intra-class the `elems` and `elseElem` are used. - `elems` and
 * `elseElem` are mapped to `ops` by first placing the `elseElem`, then all indices, then all
 * elements.
 */
@Serializable
@SerialName(ArrayInitExpr.OPERATOR_LABEL)
data class ArrayInitExpr<IndexType : Type, ElemType : Type>(
    val elements: List<Pair<Expr<IndexType>, Expr<ElemType>>>,
    val elseElem: Expr<ElemType>,
    override val type: ArrayType<IndexType, ElemType>
) : MultiaryExpr<Type, ArrayType<IndexType, ElemType>>() {

    @Suppress("UNCHECKED_CAST")
    override val ops: List<Expr<Type>> =
        listOf(elseElem as Expr<Type>) +
            elements.map { it.first as Expr<Type> } +
            elements.map { it.second as Expr<Type> }

    companion object {

        internal const val OPERATOR_LABEL = "arrayinit"

        fun <IndexType : Type, ElemType : Type> of(
            elems: List<Pair<Expr<IndexType>, Expr<ElemType>>>,
            elseElem: Expr<ElemType>,
            type: ArrayType<IndexType, ElemType>
        ) = ArrayInitExpr(elems, elseElem, type)

        @Suppress("UNCHECKED_CAST")
        fun <IndexType : Type, ElemType : Type> create(
            elems: List<Pair<Expr<out Type>, Expr<out Type>>>,
            elseElem: Expr<*>,
            type: ArrayType<*, *>
        ): ArrayInitExpr<IndexType, ElemType> =
            of(
                elems.map { Pair(it.first as Expr<IndexType>, it.second as Expr<ElemType>) },
                elseElem as Expr<ElemType>,
                type as ArrayType<IndexType, ElemType>
            )
    }

    override fun eval(`val`: Valuation): LitExpr<ArrayType<IndexType, ElemType>> =
        ArrayLitExpr.of(
            elements.map { Pair(it.first.eval(`val`), it.second.eval(`val`)) },
            elseElem,
            type
        )

    @Suppress("UNCHECKED_CAST")
    override fun with(ops: Iterable<Expr<Type>>): MultiaryExpr<Type, ArrayType<IndexType, ElemType>> {
        val size = ops.count()
        require(size % 2 == 1) { "Ops must be odd long!" }
        val elseElem: Expr<ElemType> = ops.first() as Expr<ElemType>
        val indices = mutableListOf<Expr<IndexType>>()
        val elems = mutableListOf<Expr<ElemType>>()
        ops.forEachIndexed { counter, op ->
            when {
                counter == 0 -> {}
                counter <= (size - 1) / 2 -> indices.add(op as Expr<IndexType>)
                else -> elems.add(op as Expr<ElemType>)
            }
        }
        val newOps = indices.indices.map { i ->
            indices[i] to elems[i]
        }
        return of(newOps, elseElem, type)
    }

    @Suppress("UNCHECKED_CAST")
    override fun withOps(ops: List<Expr<*>>): MultiaryExpr<Type, ArrayType<IndexType, ElemType>> =
        with(ops.map { it as Expr<Type> })

    override val operatorLabel: String = OPERATOR_LABEL

    override fun toString(): String =
        "arrayinit($elements, $elseElem, $type)"
}

