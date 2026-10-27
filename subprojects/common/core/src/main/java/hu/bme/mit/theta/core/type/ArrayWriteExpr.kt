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
import hu.bme.mit.theta.common.Tuple2
import hu.bme.mit.theta.common.Utils
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.arraytype.ArrayType
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import kotlinx.serialization.Serializable
import kotlinx.serialization.Transient

@Serializable
class ArrayWriteExpr<IndexType : Type, ElemType : Type>
private constructor(
  val array: Expr<ArrayType<IndexType, ElemType>>,
  val index: Expr<IndexType>,
  val elem: Expr<ElemType>,
) : Expr<ArrayType<IndexType, ElemType>> {

  @Transient @Volatile private var hashCode = 0

  override val type: ArrayType<IndexType, ElemType>
    get() = ArrayType.of(index.type, elem.type)

  override fun eval(valuation: Valuation): LitExpr<ArrayType<IndexType, ElemType>> {
    @Suppress("UNCHECKED_CAST")
    val arrayVal = array.eval(valuation) as ArrayLitExpr<IndexType, ElemType>
    val indexVal = index.eval(valuation)
    val elemVal = elem.eval(valuation)
    val elemList = ArrayList<Tuple2<out Expr<IndexType>, out Expr<ElemType>>>()
    for (e in arrayVal.elements) {
      if (e.get1() != indexVal) elemList.add(e)
    }
    elemList.add(Tuple2.of(indexVal, elemVal))
    return ArrayLitExpr.of(elemList, arrayVal.elseElem, arrayVal.type)
  }

  override val arity: Int
    get() = 3

  override val ops: List<Expr<*>>
    get() = ImmutableList.of(array, index, elem)

  override fun withOps(ops: List<Expr<*>>): Expr<ArrayType<IndexType, ElemType>> {
    checkArgument(ops.size == 3)
    return with(cast(ops[0], array.type), cast(ops[1], index.type), cast(ops[2], elem.type))
  }

  fun with(
    array: Expr<ArrayType<IndexType, ElemType>>,
    index: Expr<IndexType>,
    elem: Expr<ElemType>,
  ): ArrayWriteExpr<IndexType, ElemType> =
    if (this.array === array && this.index === index && elem === this.elem) this
    else of(array, index, elem)

  fun withIndex(index: Expr<IndexType>): ArrayWriteExpr<IndexType, ElemType> =
    with(array, index, elem)

  fun withElem(elem: Expr<ElemType>): ArrayWriteExpr<IndexType, ElemType> = with(array, index, elem)

  override fun hashCode(): Int {
    var result = hashCode
    if (result == 0) {
      result = HASH_SEED
      result = 31 * result + array.hashCode()
      result = 31 * result + index.hashCode()
      result = 31 * result + elem.hashCode()
      hashCode = result
    }
    return result
  }

  override fun equals(other: Any?): Boolean {
    if (other is TraceableWrapperExpr<*>) return equals(other.expr)
    if (this === other) return true
    if (other == null || javaClass != other.javaClass) return false
    val that = other as ArrayWriteExpr<*, *>
    return array == that.array && index == that.index && elem == that.elem
  }

  override fun toString(): String =
    Utils.lispStringBuilder(OPERATOR_LABEL).body().add(array).add(index).add(elem).toString()

  companion object {
    private const val HASH_SEED = 1699
    private const val OPERATOR_LABEL = "write"

    @JvmStatic
    fun <IndexType : Type, ElemType : Type> of(
      array: Expr<ArrayType<IndexType, ElemType>>,
      index: Expr<IndexType>,
      elem: Expr<ElemType>,
    ): ArrayWriteExpr<IndexType, ElemType> = ArrayWriteExpr(array, index, elem)

    @JvmStatic
    fun <IndexType : Type, ElemType : Type> create(
      array: Expr<*>,
      index: Expr<*>,
      elem: Expr<*>,
    ): ArrayWriteExpr<*, *> {
      @Suppress("UNCHECKED_CAST") val arrayType = array.type as ArrayType<IndexType, ElemType>
      return of(
        cast(array, arrayType),
        cast(index, arrayType.indexType),
        cast(elem, arrayType.elemType),
      )
    }
  }
}
