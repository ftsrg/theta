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
package hu.bme.mit.theta.core.type.fptype

import hu.bme.mit.theta.common.Utils
import hu.bme.mit.theta.core.type.*
import hu.bme.mit.theta.core.type.abstracttype.*
import java.math.BigInteger
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

@Serializable
@SerialName(FpType.TYPE_LABEL)
data class FpType(val exponent: Int, val significand: Int) :
  Equational<FpType>, Additive<FpType>, Multiplicative<FpType>, Ordered<FpType> {

  init {
    require(exponent > 1) { "Exponent must be greater than 1" }
    require(significand > 1) { "Significand must be greater than 1" }
  }

  companion object {

    internal const val TYPE_LABEL = "Fp"

    @JvmStatic fun of(exponent: Int, significand: Int): FpType = FpType(exponent, significand)
  }

  override fun Eq(leftOp: Expr<FpType>, rightOp: Expr<FpType>): EqExpr<FpType> =
    FpEqExpr(leftOp, rightOp)

  override fun Neq(leftOp: Expr<FpType>, rightOp: Expr<FpType>): NeqExpr<FpType> =
    FpNeqExpr(leftOp, rightOp)

  override fun Add(ops: Iterable<Expr<FpType>>): AddExpr<FpType> =
    FpExprs.Add(FpRoundingMode.defaultRoundingMode, ops)

  override fun Sub(leftOp: Expr<FpType>, rightOp: Expr<FpType>): SubExpr<FpType> =
    FpExprs.Sub(FpRoundingMode.defaultRoundingMode, leftOp, rightOp)

  override fun Pos(op: Expr<FpType>): PosExpr<FpType> = FpExprs.Pos(op)

  override fun Neg(op: Expr<FpType>): NegExpr<FpType> = FpExprs.Neg(op)

  override fun Mul(ops: Iterable<Expr<FpType>>): MulExpr<FpType> =
    FpExprs.Mul(FpRoundingMode.defaultRoundingMode, ops)

  override fun Div(leftOp: Expr<FpType>, rightOp: Expr<FpType>): DivExpr<FpType> =
    FpExprs.Div(FpRoundingMode.defaultRoundingMode, leftOp, rightOp)

  override fun Lt(leftOp: Expr<FpType>, rightOp: Expr<FpType>): LtExpr<FpType> =
    FpExprs.Lt(leftOp, rightOp)

  override fun Leq(leftOp: Expr<FpType>, rightOp: Expr<FpType>): LeqExpr<FpType> =
    FpExprs.Leq(leftOp, rightOp)

  override fun Gt(leftOp: Expr<FpType>, rightOp: Expr<FpType>): GtExpr<FpType> =
    FpExprs.Gt(leftOp, rightOp)

  override fun Geq(leftOp: Expr<FpType>, rightOp: Expr<FpType>): GeqExpr<FpType> =
    FpExprs.Geq(leftOp, rightOp)

  override val domainSize: DomainSize
    get() = DomainSize.of(BigInteger.TWO.pow(significand).multiply(BigInteger.TWO.pow(exponent)))

  override fun toString(): String =
    Utils.lispStringBuilder(TYPE_LABEL).add(exponent).add(significand).toString()
}
