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

import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool
import hu.bme.mit.theta.core.type.booltype.BoolType
import kotlinx.serialization.Serializable

@Serializable
object FalseExpr : BoolLitExpr() {
  private const val HASH_SEED = 712514
  private const val OPERATOR_LABEL = "false"

  @JvmStatic fun getInstance(): FalseExpr = this

  override val value: Boolean
    get() = false

  override val type: BoolType
    get() = Bool()

  override fun eval(valuation: Valuation): BoolLitExpr = this

  override fun hashCode(): Int = HASH_SEED

  override fun equals(other: Any?): Boolean =
    if (other is TraceableWrapperExpr<*>) equals(other.expr)
    else other != null && javaClass == other.javaClass

  override fun toString(): String = OPERATOR_LABEL
}
