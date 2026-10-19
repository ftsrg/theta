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
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.arraytype.ArrayType

/**
 * ArrayInitExpr is a way to specify arbitrary array 'literals' that may contain non-literal
 * elements as well. Note that while this class is a descendant of MultiaryExpr, it is used in a
 * non-standard way: - ops is only used as a generic Type type, - ops are solely used for
 * inter-object interactions, intra-class the `elems` and `elseElem` are used. - `elems` and
 * `elseElem` are mapped to `ops` by first placing the `elseElem`, then all indices, then all
 * elements.
 */
@Suppress("UNCHECKED_CAST")
class ArrayInitExpr<IndexType : Type, ElemType : Type>
private constructor(
  private val elems: List<Tuple2<Expr<IndexType>, Expr<ElemType>>>,
  elseElem: Expr<ElemType>,
  type: ArrayType<IndexType, ElemType>,
) :
  MultiaryExpr<Type, ArrayType<IndexType, ElemType>>(
    listOf(elseElem as Expr<Type>) +
      elems.map { it.get1() as Expr<Type> } +
      elems.map { it.get2() as Expr<Type> }
  ) {

  override val type: ArrayType<IndexType, ElemType> = checkNotNull(type)

  val elseElem: Expr<ElemType> = checkNotNull(elseElem)

  val elements: List<Tuple2<Expr<IndexType>, Expr<ElemType>>>
    get() = ImmutableList.copyOf(elems)

  override fun eval(valuation: Valuation): LitExpr<ArrayType<IndexType, ElemType>> =
    ArrayLitExpr.of(
      elems.map { Tuple2.of(it.get1().eval(valuation), it.get2().eval(valuation)) },
      elseElem,
      type,
    )

  override fun equals(other: Any?): Boolean {
    if (this === other) return true
    if (other == null || javaClass != other.javaClass) return false
    val that = other as ArrayInitExpr<*, *>
    return type == that.type && elems == that.elems && elseElem == that.elseElem
  }

  override fun with(ops: Iterable<Expr<Type>>): ArrayInitExpr<IndexType, ElemType> {
    val opList = ops.toList()
    val size = opList.size
    checkState(size % 2 == 1, "Ops must be odd long!")
    val half = (size - 1) / 2
    val newOps =
      (0 until half).map {
        Tuple2.of(opList[1 + it] as Expr<IndexType>, opList[1 + half + it] as Expr<ElemType>)
      }
    return keepSourceType(of(newOps, opList[0] as Expr<ElemType>, type))
  }

  override fun withOps(ops: List<Expr<*>>): ArrayInitExpr<IndexType, ElemType> =
    with(ops.map { it as Expr<Type> })

  override val hashSeed: Int
    get() = HASH_SEED

  override val operatorLabel: String
    get() = OPERATOR_LABEL

  companion object {
    private const val HASH_SEED = 241
    private const val OPERATOR_LABEL = "arrayinit"

    @JvmStatic
    fun <IndexType : Type, ElemType : Type> of(
      elems: List<Tuple2<Expr<IndexType>, Expr<ElemType>>>,
      elseElem: Expr<ElemType>,
      type: ArrayType<IndexType, ElemType>,
    ): ArrayInitExpr<IndexType, ElemType> = ArrayInitExpr(elems, elseElem, type)

    @JvmStatic
    fun <IndexType : Type, ElemType : Type> create(
      elems: List<Tuple2<Expr<out Type>, Expr<out Type>>>,
      elseElem: Expr<*>,
      type: ArrayType<*, *>,
    ): ArrayInitExpr<IndexType, ElemType> =
      of(
        elems.map { Tuple2.of(it.get1() as Expr<IndexType>, it.get2() as Expr<ElemType>) },
        elseElem as Expr<ElemType>,
        type as ArrayType<IndexType, ElemType>,
      )
  }
}
