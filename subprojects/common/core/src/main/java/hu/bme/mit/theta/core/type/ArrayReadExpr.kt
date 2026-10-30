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

import com.google.common.base.Preconditions.checkArgument
import com.google.common.collect.ImmutableList
import hu.bme.mit.theta.common.Utils
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.arraytype.ArrayType
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import kotlinx.serialization.Serializable
import kotlinx.serialization.Transient

@Serializable
class ArrayReadExpr<IndexType : Type, ElemType : Type>
private constructor(val array: Expr<ArrayType<IndexType, ElemType>>, val index: Expr<IndexType>) :
  Expr<ElemType> {

  @Transient @Volatile private var hashCode = 0

  override val type: ElemType
    get() = array.type.elemType

  override fun eval(valuation: Valuation): LitExpr<ElemType> {
    @Suppress("UNCHECKED_CAST")
    val arrayVal = array.eval(valuation) as ArrayLitExpr<IndexType, ElemType>
    val indexVal = index.eval(valuation)
    for (elem in arrayVal.elements) {
      if (elem.get1() == indexVal) return elem.get2()
    }
    return arrayVal.elseElem
  }

  override val arity: Int
    get() = 2

  override val ops: List<Expr<*>>
    get() = ImmutableList.of(array, index)

  override fun withOps(ops: List<Expr<*>>): Expr<ElemType> {
    checkArgument(ops.size == 2)
    return with(cast(ops[0], array.type), cast(ops[1], index.type))
  }

  fun with(
    array: Expr<ArrayType<IndexType, ElemType>>,
    index: Expr<IndexType>,
  ): ArrayReadExpr<IndexType, ElemType> =
    if (this.array === array && this.index === index) this else of(array, index)

  fun withArray(array: Expr<ArrayType<IndexType, ElemType>>): ArrayReadExpr<IndexType, ElemType> =
    with(array, index)

  fun withIndex(index: Expr<IndexType>): ArrayReadExpr<IndexType, ElemType> = with(array, index)

  override fun hashCode(): Int {
    var result = hashCode
    if (result == 0) {
      result = HASH_SEED
      result = 31 * result + array.hashCode()
      result = 31 * result + index.hashCode()
      hashCode = result
    }
    return result
  }

  override fun equals(other: Any?): Boolean {
    if (other is TraceableWrapperExpr<*>) return equals(other.expr)
    if (this === other) return true
    if (other == null || javaClass != other.javaClass) return false
    val that = other as ArrayReadExpr<*, *>
    return array == that.array && index == that.index
  }

  override fun toString(): String =
    Utils.lispStringBuilder(OPERATOR_LABEL).body().add(array).add(index).toString()

  companion object {
    private const val HASH_SEED = 1321
    private const val OPERATOR_LABEL = "read"

    @JvmStatic
    fun <IndexType : Type, ElemType : Type> of(
      array: Expr<ArrayType<IndexType, ElemType>>,
      index: Expr<IndexType>,
    ): ArrayReadExpr<IndexType, ElemType> = ArrayReadExpr(array, index)

    @JvmStatic
    fun <IndexType : Type, ElemType : Type> create(
      array: Expr<*>,
      index: Expr<*>,
    ): ArrayReadExpr<*, *> {
      @Suppress("UNCHECKED_CAST") val arrayType = array.type as ArrayType<IndexType, ElemType>
      return of(cast(array, arrayType), cast(index, arrayType.indexType))
    }
  }
}
