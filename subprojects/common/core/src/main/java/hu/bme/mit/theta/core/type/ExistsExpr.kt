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

import com.google.common.collect.ImmutableList
import hu.bme.mit.theta.core.decl.ParamDecl
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import kotlinx.serialization.Serializable

@Serializable
class ExistsExpr
private constructor(override val paramDecls: List<ParamDecl<*>>, override val op: Expr<BoolType>) :
  QuantifiedExpr() {

  override fun eval(valuation: Valuation): LitExpr<BoolType> = throw UnsupportedOperationException()

  override fun with(op: Expr<BoolType>): ExistsExpr =
    if (op === this.op) this else of(paramDecls, op)

  override val hashSeed: Int
    get() = HASH_SEED

  override val operatorLabel: String
    get() = OPERATOR_LABEL

  companion object {
    private const val HASH_SEED = 7993
    private const val OPERATOR_LABEL = "exists"

    @JvmStatic
    fun of(paramDecls: Iterable<ParamDecl<*>>, op: Expr<BoolType>): ExistsExpr =
      ExistsExpr(ImmutableList.copyOf(paramDecls), op)

    @JvmStatic
    fun create(paramDecls: Iterable<ParamDecl<*>>, op: Expr<*>): ExistsExpr =
      of(paramDecls, cast(op, Bool()))
  }
}
