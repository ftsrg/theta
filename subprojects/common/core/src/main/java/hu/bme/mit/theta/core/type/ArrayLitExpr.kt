/*
 *  Copyright 2026 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.core.type

import com.google.common.base.Preconditions.checkNotNull
import com.google.common.base.Preconditions.checkState
import com.google.common.collect.ImmutableList
import hu.bme.mit.theta.common.Tuple2
import hu.bme.mit.theta.common.Utils
import hu.bme.mit.theta.core.model.ImmutableValuation
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.arraytype.ArrayType
import hu.bme.mit.theta.core.utils.ExprSimplifier

@Suppress("UNCHECKED_CAST")
class ArrayLitExpr<IndexType : Type, ElemType : Type>
private constructor(
  elems: List<Tuple2<out Expr<IndexType>, out Expr<ElemType>>>,
  elseElem: Expr<ElemType>,
  type: ArrayType<IndexType, ElemType>,
) : NullaryExpr<ArrayType<IndexType, ElemType>>(), LitExpr<ArrayType<IndexType, ElemType>> {

  override val type: ArrayType<IndexType, ElemType> = checkNotNull(type)

  val elseElem: LitExpr<ElemType>

  private val elems: List<Tuple2<LitExpr<IndexType>, LitExpr<ElemType>>>

  @Volatile private var hashCode = 0

  init {
    val exprSimplifier = ExprSimplifier.create()
    val simplifiedElem = exprSimplifier.simplify(checkNotNull(elseElem), ImmutableValuation.empty())
    checkState(simplifiedElem is LitExpr<*>, "ArrayLitExprs shall only contain literal values!")
    this.elseElem = simplifiedElem as LitExpr<ElemType>
    this.elems =
      checkNotNull(elems).map { elem ->
        val index = exprSimplifier.simplify(elem.get1(), ImmutableValuation.empty())
        val element = exprSimplifier.simplify(elem.get2(), ImmutableValuation.empty())
        checkState(
          index is LitExpr<*> && element is LitExpr<*>,
          "ArrayLitExprs shall only contain literal values",
        )
        Tuple2.of(index as LitExpr<IndexType>, element as LitExpr<ElemType>)
      }
  }

  val elements: List<Tuple2<LitExpr<IndexType>, LitExpr<ElemType>>>
    get() = ImmutableList.copyOf(elems)

  override fun eval(valuation: Valuation): LitExpr<ArrayType<IndexType, ElemType>> = this

  override fun hashCode(): Int {
    var tmp = hashCode
    if (tmp == 0) {
      tmp = HASH_SEED
      tmp = 31 * tmp + type.hashCode()
      for (elem in elems) {
        tmp = 31 * tmp + elem.hashCode()
      }
      hashCode = tmp
    }
    return tmp
  }

  override fun equals(other: Any?): Boolean {
    if (this === other) return true
    if (other == null || javaClass != other.javaClass) return false
    val that = other as ArrayLitExpr<*, *>
    return type == that.type && elems == that.elems && elseElem == that.elseElem
  }

  override fun toString(): String =
    Utils.lispStringBuilder(OPERATOR_LABEL)
      .body()
      .addAll(elems.map { String.format("(%s %s)", it.get1(), it.get2()) })
      .add(String.format("(default %s)", elseElem))
      .toString()

  companion object {
    private const val HASH_SEED = 229
    private const val OPERATOR_LABEL = "array"

    @JvmStatic
    fun <IndexType : Type, ElemType : Type> of(
      elems: List<Tuple2<out Expr<IndexType>, out Expr<ElemType>>>,
      elseElem: Expr<ElemType>,
      type: ArrayType<IndexType, ElemType>,
    ): ArrayLitExpr<IndexType, ElemType> = ArrayLitExpr(elems, elseElem, type)
  }
}
