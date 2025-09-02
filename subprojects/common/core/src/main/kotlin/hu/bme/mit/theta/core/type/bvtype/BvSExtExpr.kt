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
package hu.bme.mit.theta.core.type.bvtype

import hu.bme.mit.theta.common.Utils
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.utils.TypeUtils.castBv
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

@Serializable
@SerialName("BvSExt")
data class BvSExtExpr(val op: Expr<BvType>, val extendType: BvType) : Expr<BvType> {

  init {
    check(extendType.size >= op.type.size)
  }

  companion object {

    private const val OPERATOR_LABEL = "bv_sign_extend"

    @JvmStatic fun of(op: Expr<BvType>, extendType: BvType) = BvSExtExpr(op, extendType)

    @JvmStatic fun create(op: Expr<*>, extendType: BvType) = BvSExtExpr(castBv(op), extendType)
  }

  override val arity: Int = 1
  override val type: BvType = extendType
  override val ops: List<Expr<*>> = listOf(op)

  override fun eval(`val`: Valuation): LitExpr<BvType> {
    val bvLitExpr = op.eval(`val`) as BvLitExpr
    return bvLitExpr.sext(extendType)
  }

  override fun withOps(ops: List<Expr<*>>): Expr<BvType> {
    require(ops.size == 1)
    return of(castBv(ops[0]), extendType)
  }

  override fun toString(): String =
    Utils.lispStringBuilder(OPERATOR_LABEL).body().add(op).add(type).toString()
}
