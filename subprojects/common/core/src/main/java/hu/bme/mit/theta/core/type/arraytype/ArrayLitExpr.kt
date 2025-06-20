package hu.bme.mit.theta.core.type.arraytype

import hu.bme.mit.theta.common.Utils
import hu.bme.mit.theta.core.model.ImmutableValuation
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.NullaryExpr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.utils.ExprSimplifier
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

/**
 * Literal array expression for array types, containing only literal values.
 */
@Serializable
@SerialName("ArrayLitExpr")
data class ArrayLitExpr<IndexType : Type, ElemType : Type> private constructor(
    val elements: List<Pair<LitExpr<IndexType>, LitExpr<ElemType>>>,
    val elseElem: LitExpr<ElemType>,
    override val type: ArrayType<IndexType, ElemType>
) : NullaryExpr<ArrayType<IndexType, ElemType>>(), LitExpr<ArrayType<IndexType, ElemType>> {

    companion object {

        private const val OPERATOR_LABEL = "array"

        fun <IndexType : Type, ElemType : Type> of(
            elems: List<Pair<Expr<IndexType>, Expr<ElemType>>>,
            elseElem: Expr<ElemType>,
            type: ArrayType<IndexType, ElemType>
        ): ArrayLitExpr<IndexType, ElemType> {
            val simplifier = ExprSimplifier.create()
            val simplifiedElse = simplifier.simplify(elseElem, ImmutableValuation.empty())
            require(simplifiedElse is LitExpr<*>) { "ArrayLitExprs shall only contain literal values!" }
            val litElse = simplifiedElse as LitExpr<ElemType>
            val litElems = elems.map {
                val idx = simplifier.simplify(it.first, ImmutableValuation.empty())
                val elem = simplifier.simplify(it.second, ImmutableValuation.empty())
                require(idx is LitExpr<*> && elem is LitExpr<*>) { "ArrayLitExprs shall only contain literal values!" }
                Pair(idx as LitExpr<IndexType>, elem as LitExpr<ElemType>)
            }
            return ArrayLitExpr(litElems, litElse, type)
        }
    }

    override fun eval(`val`: Valuation): LitExpr<ArrayType<IndexType, ElemType>> = this

    override fun toString(): String =
        Utils.lispStringBuilder(OPERATOR_LABEL)
            .body()
            .addAll(elements.map { "(${it.first} ${it.second})" })
            .add("(default $elseElem)")
            .toString()
}

