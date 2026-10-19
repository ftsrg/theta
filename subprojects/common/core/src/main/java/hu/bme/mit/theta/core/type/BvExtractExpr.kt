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
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.core.utils.TypeUtils.castBv

class BvExtractExpr
private constructor(val bitvec: Expr<BvType>, val from: IntLitExpr, val until: IntLitExpr) :
  AbstractExpr<BvType>() {

  @Volatile private var hashCode = 0

  init {
    checkArgument(from.value.signum() >= 0)
    checkArgument(until.value.signum() >= 0)
    checkArgument(until.value > from.value)
  }

  override val ops: List<Expr<*>>
    get() = ImmutableList.of(bitvec, from, until)

  override val arity: Int
    get() = 3

  override val type: BvType
    get() = bitvec.type.withSize(until.value.subtract(from.value).toInt())

  override fun eval(valuation: Valuation): LitExpr<BvType> =
    (bitvec.eval(valuation) as BvLitExpr).extract(from, until)

  override fun withOps(ops: List<Expr<*>>): Expr<BvType> {
    checkArgument(ops.size == 3)
    val newBitvec = castBv(ops[0])
    val newFrom = cast(ops[1], Int()) as IntLitExpr
    val newUntil = cast(ops[2], Int()) as IntLitExpr
    return if (bitvec == newBitvec && from == newFrom && until == newUntil) this
    else keepSourceType(of(newBitvec, newFrom, newUntil))
  }

  override fun hashCode(): Int {
    var result = hashCode
    if (result == 0) {
      result = HASH_SEED
      result = 31 * result + bitvec.hashCode()
      result = 31 * result + from.hashCode()
      result = 31 * result + until.hashCode()
      hashCode = result
    }
    return result
  }

  override fun equals(other: Any?): Boolean {
    if (this === other) return true
    if (other == null || javaClass != other.javaClass) return false
    val that = other as BvExtractExpr
    return bitvec == that.bitvec && from == that.from && until == that.until
  }

  override fun toString(): String =
    Utils.lispStringBuilder(OPERATOR_LABEL).body().add(bitvec).add(from).add(until).toString()

  companion object {
    private const val HASH_SEED = 6586
    private const val OPERATOR_LABEL = "extract"

    @JvmStatic
    fun of(bitvec: Expr<BvType>, from: IntLitExpr, until: IntLitExpr): BvExtractExpr =
      BvExtractExpr(bitvec, from, until)

    @JvmStatic
    fun create(bitvec: Expr<*>, from: Expr<*>, until: Expr<*>): BvExtractExpr =
      of(castBv(bitvec), cast(from, Int()) as IntLitExpr, cast(until, Int()) as IntLitExpr)
  }
}
