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
package hu.bme.mit.theta.core.type.abstracttype

import hu.bme.mit.theta.core.type.BinaryExpr
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import kotlinx.serialization.Serializable

/** Abstract base class for not-equal (!=) expressions over equational types. */
@Serializable
abstract class NeqExpr<OpType : Equational<OpType>> : BinaryExpr<OpType, BoolType>() {

  companion object {
    private const val OPERATOR_LABEL = "/="

    @JvmStatic
    fun <OpType : Equational<OpType>> create2(leftOp: Expr<*>, rightOp: Expr<*>): NeqExpr<*> {
      @Suppress("UNCHECKED_CAST") val type = leftOp.type as OpType
      val newLeftOp = cast(leftOp, type)
      val newRightOp = cast(rightOp, type)
      return type.Neq(newLeftOp, newRightOp)
    }
  }

  override val operatorLabel: String
    get() = OPERATOR_LABEL

  override val type: BoolType = Bool()
}
