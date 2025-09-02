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
import hu.bme.mit.theta.core.utils.TypeUtils
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

@Serializable
@SerialName("BvConcat")
data class BvConcatExpr(override val ops: List<Expr<BvType>>) : Expr<BvType> {

  init {
    check(ops.isNotEmpty())
  }

  companion object {

    private const val OPERATOR_LABEL = "++"

    @JvmStatic fun of(ops: Iterable<Expr<BvType>>) = BvConcatExpr(ops.toList())

    @JvmStatic fun create(ops: List<Expr<*>>) = BvConcatExpr(ops.map { TypeUtils.castBv(it) })
  }

  override val type: BvType = BvType.of(ops.sumOf { it.type.size })

  override fun eval(`val`: Valuation): BvLitExpr =
    ops.drop(1).fold(ops[0].eval(`val`) as BvLitExpr) { acc, op ->
      acc.concat(op.eval(`val`) as BvLitExpr)
    }

  override fun withOps(ops: List<Expr<*>>): Expr<BvType> = of(ops.map { TypeUtils.castBv(it) })

  override fun toString(): String =
    Utils.lispStringBuilder(OPERATOR_LABEL).body().addAll(ops).toString()
}
