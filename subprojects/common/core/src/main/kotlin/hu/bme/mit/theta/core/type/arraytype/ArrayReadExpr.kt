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
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

/** Read expression for array types. */
@Serializable
@SerialName("ArrayReadExpr")
data class ArrayReadExpr<IndexType : Type, ElemType : Type>(
  val array: Expr<ArrayType<IndexType, ElemType>>,
  val index: Expr<IndexType>,
) : Expr<ElemType> {

  companion object {

    private const val OPERATOR_LABEL = "read"

    @JvmStatic
    fun <IndexType : Type, ElemType : Type> of(
      array: Expr<ArrayType<IndexType, ElemType>>,
      index: Expr<IndexType>,
    ) = ArrayReadExpr(array, index)

    @JvmStatic
    @Suppress("UNCHECKED_CAST")
    fun <IndexType : Type, ElemType : Type> create(
      array: Expr<*>,
      index: Expr<*>,
    ): ArrayReadExpr<IndexType, ElemType> {
      val arrayType = array.type as ArrayType<IndexType, ElemType>
      val newArray = cast(array, arrayType)
      val newIndex = cast(index, arrayType.indexType)
      return of(newArray, newIndex)
    }
  }

  override val ops: List<Expr<*>>
    get() = listOf(array, index)

  override val type: ElemType = array.type.elemType

  override fun eval(`val`: Valuation): LitExpr<ElemType> {
    val arrayVal = array.eval(`val`) as ArrayLitExpr<IndexType, ElemType>
    val indexVal = index.eval(`val`)
    arrayVal.elements.forEach { elem -> if (elem.first == indexVal) return elem.second }
    return arrayVal.elseElem
  }

  override fun withOps(ops: List<Expr<*>>): Expr<ElemType> {
    require(ops.size == 2)
    val newArray = cast(ops[0], array.type)
    val newIndex = cast(ops[1], index.type)
    return with(newArray, newIndex)
  }

  fun with(
    array: Expr<ArrayType<IndexType, ElemType>>,
    index: Expr<IndexType>,
  ): ArrayReadExpr<IndexType, ElemType> =
    if (this.array === array && this.index === index) {
      this
    } else {
      of(array, index)
    }

  fun withArray(array: Expr<ArrayType<IndexType, ElemType>>): ArrayReadExpr<IndexType, ElemType> =
    with(array, index)

  fun withIndex(index: Expr<IndexType>): ArrayReadExpr<IndexType, ElemType> = with(array, index)

  override fun toString(): String =
    Utils.lispStringBuilder(OPERATOR_LABEL).body().add(array).add(index).toString()
}
