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
import hu.bme.mit.theta.core.type.bvtype.BvType
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.core.utils.BvUtils
import hu.bme.mit.theta.core.utils.TypeUtils.castBv

class BvToIntExpr private constructor(op: Expr<BvType>, val isSigned: Boolean) :
  CastExpr<BvType, IntType>(op) {

  override val type: IntType
    get() = Int()

  override fun eval(valuation: Valuation): IntLitExpr {
    val opVal = op.eval(valuation) as BvLitExpr
    return if (isSigned) IntLitExpr.of(BvUtils.signedBvLitExprToBigInteger(opVal))
    else IntLitExpr.of(BvUtils.neutralBvLitExprToBigInteger(opVal))
  }

  /** Re-derives the signedness from the new operand's type. */
  override fun with(op: Expr<BvType>): BvToIntExpr =
    if (op === this.op) this else keepSourceType(of(op))

  override fun equals(other: Any?): Boolean {
    if (this === other) return true
    if (other == null || javaClass != other.javaClass) return false
    val that = other as BvToIntExpr
    return op == that.op && isSigned == that.isSigned
  }

  override fun hashCode(): Int = 37 * hashSeed + op.hashCode() + isSigned.hashCode()

  fun withSignedness(signed: Boolean): BvToIntExpr =
    if (signed == isSigned) this else keepSourceType(create(op, signed))

  override val hashSeed: Int
    get() = HASH_SEED

  override val operatorLabel: String
    get() = OPERATOR_LABEL

  companion object {
    private const val HASH_SEED = 9903
    private const val OPERATOR_LABEL = "to_int"

    @JvmStatic fun of(op: Expr<BvType>, signed: Boolean): BvToIntExpr = BvToIntExpr(op, signed)

    @JvmStatic fun of(op: Expr<BvType>): BvToIntExpr = BvToIntExpr(op, op.type.signed)

    @JvmStatic fun create(op: Expr<*>, signed: Boolean): BvToIntExpr = of(castBv(op), signed)

    @JvmStatic
    fun create(op: Expr<*>): BvToIntExpr {
      val newOp = castBv(op)
      return create(newOp, newOp.type.signed)
    }
  }
}
