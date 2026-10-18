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

class BvSExtExpr private constructor(val op: Expr<BvType>, val extendType: BvType) :
  AbstractExpr<BvType>() {

  @Volatile private var hashCode = 0

  init {
    checkArgument(extendType.size >= op.type.size)
  }

  override val arity: Int
    get() = 1

  override val type: BvType
    get() = extendType

  override fun eval(valuation: Valuation): LitExpr<BvType> =
    (op.eval(valuation) as BvLitExpr).sext(extendType)

  override val ops: List<Expr<*>>
    get() = ImmutableList.of(op)

  override fun withOps(ops: List<Expr<*>>): Expr<BvType> {
    checkArgument(ops.size == 1)
    return keepSourceType(of(castBv(ops[0]), extendType))
  }

  override fun hashCode(): Int {
    var result = hashCode
    if (result == 0) {
      result = HASH_SEED
      result = 31 * result + op.hashCode()
      result = 31 * result + extendType.hashCode()
      hashCode = result
    }
    return result
  }

  override fun equals(other: Any?): Boolean {
    if (this === other) return true
    if (other == null || javaClass != other.javaClass) return false
    val that = other as BvSExtExpr
    return ops == that.ops && type == that.type
  }

  override fun toString(): String =
    Utils.lispStringBuilder(OPERATOR_LABEL).body().add(op).add(type).toString()

  companion object {
    private const val HASH_SEED = 6126
    private const val OPERATOR_LABEL = "bv_sign_extend"

    @JvmStatic fun of(op: Expr<BvType>, extendType: BvType): BvSExtExpr = BvSExtExpr(op, extendType)

    @JvmStatic
    fun create(op: Expr<*>, extendType: BvType): BvSExtExpr = BvSExtExpr(castBv(op), extendType)
  }
}
