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
import hu.bme.mit.theta.core.type.bvtype.BvType
import hu.bme.mit.theta.core.utils.TypeUtils.castBv
import kotlinx.serialization.Serializable
import kotlinx.serialization.Transient

@Serializable
class BvConcatExpr private constructor(override val ops: List<Expr<BvType>>) : Expr<BvType> {

  @Transient @Volatile private var hashCode = 0

  override val arity: Int
    get() = ops.size

  override val type: BvType
    get() = BvType.of(ops.sumOf { it.type.size })

  override fun eval(valuation: Valuation): BvLitExpr =
    ops.drop(1).fold(ops[0].eval(valuation) as BvLitExpr) { acc, op ->
      acc.concat(op.eval(valuation) as BvLitExpr)
    }

  override fun withOps(ops: List<Expr<*>>): Expr<BvType> {
    checkArgument(ops.isNotEmpty())
    return of(ops.map { castBv(it) })
  }

  override fun hashCode(): Int {
    var result = hashCode
    if (result == 0) {
      result = HASH_SEED
      result = 31 * result + ops.hashCode()
      hashCode = result
    }
    return result
  }

  override fun equals(other: Any?): Boolean =
    if (other is TraceableWrapperExpr<*>) equals(other.expr)
    else
      this === other ||
        (other != null && javaClass == other.javaClass && ops == (other as BvConcatExpr).ops)

  override fun toString(): String =
    Utils.lispStringBuilder(OPERATOR_LABEL).body().addAll(ops).toString()

  companion object {
    private const val HASH_SEED = 8264
    private const val OPERATOR_LABEL = "++"

    @JvmStatic
    fun of(ops: Iterable<Expr<BvType>>): BvConcatExpr {
      checkArgument(ops.iterator().hasNext())
      return BvConcatExpr(ImmutableList.copyOf(ops))
    }

    @JvmStatic fun create(ops: List<Expr<*>>): BvConcatExpr = of(ops.map { castBv(it) })
  }
}
