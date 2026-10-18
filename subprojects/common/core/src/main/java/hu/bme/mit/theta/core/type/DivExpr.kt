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

import hu.bme.mit.theta.core.type.abstracttype.Multiplicative
import hu.bme.mit.theta.core.utils.TypeUtils.cast

sealed class DivExpr<ExprType : Multiplicative<ExprType>>
protected constructor(leftOp: Expr<ExprType>, rightOp: Expr<ExprType>) :
  BinaryExpr<ExprType, ExprType>(leftOp, rightOp) {

  companion object {
    @JvmStatic
    fun <ExprType : Multiplicative<ExprType>> create2(
      leftOp: Expr<*>,
      rightOp: Expr<*>,
    ): DivExpr<*> {
      @Suppress("UNCHECKED_CAST") val type = leftOp.type as ExprType
      return type.Div(cast(leftOp, type), cast(rightOp, type))
    }
  }
}
