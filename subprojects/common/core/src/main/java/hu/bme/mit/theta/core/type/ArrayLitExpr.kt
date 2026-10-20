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
import hu.bme.mit.theta.core.serialization.Tuple2Serializer
import hu.bme.mit.theta.core.type.arraytype.ArrayType
import hu.bme.mit.theta.core.utils.ExprSimplifier
import kotlinx.serialization.Serializable
import kotlinx.serialization.Transient

@Suppress("UNCHECKED_CAST")
@Serializable
class ArrayLitExpr<IndexType : Type, ElemType : Type>
private constructor(
  val elements:
    List<
      @Serializable(with = Tuple2Serializer::class)
      Tuple2<LitExpr<IndexType>, LitExpr<ElemType>>
    >,
  val elseElem: LitExpr<ElemType>,
  override val type: ArrayType<IndexType, ElemType>,
) : NullaryExpr<ArrayType<IndexType, ElemType>>(), LitExpr<ArrayType<IndexType, ElemType>> {

  @Transient @Volatile private var hashCode = 0

  override fun eval(valuation: Valuation): LitExpr<ArrayType<IndexType, ElemType>> = this

  override fun hashCode(): Int {
    var tmp = hashCode
    if (tmp == 0) {
      tmp = HASH_SEED
      tmp = 31 * tmp + type.hashCode()
      for (elem in elements) {
        tmp = 31 * tmp + elem.hashCode()
      }
      hashCode = tmp
    }
    return tmp
  }

  override fun equals(other: Any?): Boolean {
    if (other is TraceableWrapperExpr<*>) return equals(other.expr)
    if (this === other) return true
    if (other == null || javaClass != other.javaClass) return false
    val that = other as ArrayLitExpr<*, *>
    return type == that.type && elements == that.elements && elseElem == that.elseElem
  }

  override fun toString(): String =
    Utils.lispStringBuilder(OPERATOR_LABEL)
      .body()
      .addAll(elements.map { String.format("(%s %s)", it.get1(), it.get2()) })
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
    ): ArrayLitExpr<IndexType, ElemType> {
      val exprSimplifier = ExprSimplifier.create()
      // An element is a plain value: traceability info is not kept inside a literal.
      fun <T : Type> literal(expr: Expr<T>): LitExpr<T> {
        val simplified = exprSimplifier.simplify(expr, ImmutableValuation.empty()).unwrapTraceable()
        checkState(simplified is LitExpr<*>, "ArrayLitExprs shall only contain literal values")
        return simplified as LitExpr<T>
      }
      return ArrayLitExpr(
        ImmutableList.copyOf(elems.map { Tuple2.of(literal(it.get1()), literal(it.get2())) }),
        literal(elseElem),
        checkNotNull(type),
      )
    }
  }
}
