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
package hu.bme.mit.theta.core.type.booltype

import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.NullaryExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

/** Abstract base class for boolean literal expressions. */
@Serializable
sealed class BoolLitExpr : NullaryExpr<BoolType>(), LitExpr<BoolType> {

  abstract val value: Boolean

  override val type: BoolType = Bool()

  override fun eval(`val`: Valuation): BoolLitExpr = this

  companion object {
    @JvmStatic fun of(value: Boolean): BoolLitExpr = if (value) TrueExpr else FalseExpr
  }
}

@Serializable
@SerialName("False")
object FalseExpr : BoolLitExpr() {

  @JvmStatic fun getInstance(): FalseExpr = this

  override val value: Boolean = false

  override fun toString(): String = "false"
}

@Serializable
@SerialName("True")
object TrueExpr : BoolLitExpr() {

  @JvmStatic fun getInstance(): TrueExpr = this

  override val value: Boolean = true

  override fun toString(): String = "true"
}
