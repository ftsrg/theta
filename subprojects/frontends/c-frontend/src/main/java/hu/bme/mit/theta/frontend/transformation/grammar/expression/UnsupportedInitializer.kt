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
package hu.bme.mit.theta.frontend.transformation.grammar.expression

import com.google.common.base.Preconditions.checkArgument
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.ForeignExpr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.frontend.UnsupportedFrontendElementException
import kotlinx.serialization.Serializable

@Serializable
class UnsupportedInitializer : ForeignExpr<IntType>() {

  override val arity: Int
    get() = 0

  override val ops: List<Expr<*>>
    get() = listOf()

  override fun withOps(ops: List<Expr<*>>): UnsupportedInitializer {
    checkArgument(ops.isEmpty())
    return this
  }

  override val type: IntType
    get() = Int()

  override fun eval(valuation: Valuation): LitExpr<IntType> =
    throw UnsupportedFrontendElementException(
      "UnsupportedInitializer expressions are not supported."
    )

  override fun toString(): String = "UnsupportedInitializer"
}
