/*
 *  Copyright 2025 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
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

/** Literal array expression for array types, containing only literal values. */
@Serializable
@SerialName("ArrayLitExpr")
data class ArrayLitExpr<IndexType : Type, ElemType : Type>(
  val elements: List<Pair<LitExpr<IndexType>, LitExpr<ElemType>>>,
  val elseElem: LitExpr<ElemType>,
  override val type: ArrayType<IndexType, ElemType>,
) : NullaryExpr<ArrayType<IndexType, ElemType>>(), LitExpr<ArrayType<IndexType, ElemType>> {

  companion object {

    private const val OPERATOR_LABEL = "array"

    @JvmStatic
    fun <IndexType : Type, ElemType : Type> of(
      elems: List<Pair<Expr<IndexType>, Expr<ElemType>>>,
      elseElem: Expr<ElemType>,
      type: ArrayType<IndexType, ElemType>,
    ): ArrayLitExpr<IndexType, ElemType> {
      val simplifier = ExprSimplifier.create()
      val simplifiedElse = simplifier.simplify(elseElem, ImmutableValuation.empty())
      require(simplifiedElse is LitExpr<*>) { "ArrayLitExprs shall only contain literal values!" }
      val litElse = simplifiedElse as LitExpr<ElemType>
      val litElems =
        elems.map {
          val idx = simplifier.simplify(it.first, ImmutableValuation.empty())
          val elem = simplifier.simplify(it.second, ImmutableValuation.empty())
          require(idx is LitExpr<*> && elem is LitExpr<*>) {
            "ArrayLitExprs shall only contain literal values!"
          }
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
