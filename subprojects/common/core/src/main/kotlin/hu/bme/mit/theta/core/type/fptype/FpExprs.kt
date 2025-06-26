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

import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr
import hu.bme.mit.theta.core.type.bvtype.BvType

@Suppress("FunctionName")
object FpExprs {

  @JvmStatic fun FpType(exponent: Int, significand: Int) = FpType.of(exponent, significand)

  @JvmStatic
  fun Fp(hidden: Boolean, exponent: BvLitExpr, significand: BvLitExpr) =
    FpLitExpr(hidden, exponent, significand)

  @JvmStatic
  fun NaN(fpType: FpType): FpLitExpr {
    val exponent = BooleanArray(fpType.exponent) { true }
    val significand = BooleanArray(fpType.significand - 1) { true }
    return Fp(false, BvLitExpr.of(exponent), BvLitExpr.of(significand))
  }

  @JvmStatic
  fun PositiveInfinity(fpType: FpType): FpLitExpr {
    val exponent = BooleanArray(fpType.exponent) { true }
    val significand = BooleanArray(fpType.significand - 1) { false }
    return Fp(false, BvLitExpr.of(exponent), BvLitExpr.of(significand))
  }

  @JvmStatic
  fun NegativeInfinity(fpType: FpType): FpLitExpr {
    val exponent = BooleanArray(fpType.exponent) { true }
    val significand = BooleanArray(fpType.significand - 1) { false }
    return Fp(true, BvLitExpr.of(exponent), BvLitExpr.of(significand))
  }

  @JvmStatic
  fun PositiveZero(fpType: FpType): FpLitExpr {
    val exponent = BooleanArray(fpType.exponent) { false }
    val significand = BooleanArray(fpType.significand - 1) { false }
    return Fp(false, BvLitExpr.of(exponent), BvLitExpr.of(significand))
  }

  @JvmStatic
  fun NegativeZero(fpType: FpType): FpLitExpr {
    val exponent = BooleanArray(fpType.exponent) { false }
    val significand = BooleanArray(fpType.significand - 1) { false }
    return Fp(true, BvLitExpr.of(exponent), BvLitExpr.of(significand))
  }

  @JvmStatic
  fun Add(roundingMode: FpRoundingMode, ops: Iterable<Expr<FpType>>) =
    FpAddExpr.of(roundingMode, ops)

  @JvmStatic
  fun Sub(roundingMode: FpRoundingMode, leftOp: Expr<FpType>, rightOp: Expr<FpType>) =
    FpSubExpr(roundingMode, leftOp, rightOp)

  @JvmStatic fun Pos(op: Expr<FpType>) = FpPosExpr(op)

  @JvmStatic fun Neg(op: Expr<FpType>) = FpNegExpr(op)

  @JvmStatic
  fun Mul(roundingMode: FpRoundingMode, ops: Iterable<Expr<FpType>>) =
    FpMulExpr.of(roundingMode, ops)

  @JvmStatic
  fun Div(roundingMode: FpRoundingMode, leftOp: Expr<FpType>, rightOp: Expr<FpType>) =
    FpDivExpr(roundingMode, leftOp, rightOp)

  @JvmStatic fun Rem(leftOp: Expr<FpType>, rightOp: Expr<FpType>) = FpRemExpr(leftOp, rightOp)

  @JvmStatic fun Abs(op: Expr<FpType>) = FpAbsExpr(op)

  @JvmStatic
  fun FromBv(roundingMode: FpRoundingMode, op: Expr<BvType>, fpType: FpType, signed: Boolean) =
    FpFromBvExpr(roundingMode, op, fpType, signed)

  @JvmStatic fun Eq(leftOp: Expr<FpType>, rightOp: Expr<FpType>) = FpEqExpr(leftOp, rightOp)

  @JvmStatic
  fun FpAssign(leftOp: Expr<FpType>, rightOp: Expr<FpType>) = FpAssignExpr(leftOp, rightOp)

  @JvmStatic fun Neq(leftOp: Expr<FpType>, rightOp: Expr<FpType>) = FpNeqExpr(leftOp, rightOp)

  @JvmStatic fun Gt(leftOp: Expr<FpType>, rightOp: Expr<FpType>) = FpGtExpr(leftOp, rightOp)

  @JvmStatic fun Geq(leftOp: Expr<FpType>, rightOp: Expr<FpType>) = FpGeqExpr(leftOp, rightOp)

  @JvmStatic fun Lt(leftOp: Expr<FpType>, rightOp: Expr<FpType>) = FpLtExpr(leftOp, rightOp)

  @JvmStatic fun Leq(leftOp: Expr<FpType>, rightOp: Expr<FpType>) = FpLeqExpr(leftOp, rightOp)

  @JvmStatic fun IsNan(op: Expr<FpType>) = FpIsNanExpr(op)

  @JvmStatic fun IsInfinite(op: Expr<FpType>) = FpIsInfiniteExpr(op)

  @JvmStatic
  fun RoundToIntegral(roundingMode: FpRoundingMode, op: Expr<FpType>) =
    FpRoundToIntegralExpr(roundingMode, op)

  @JvmStatic fun Sqrt(roundingMode: FpRoundingMode, op: Expr<FpType>) = FpSqrtExpr(roundingMode, op)

  @JvmStatic fun Max(leftOp: Expr<FpType>, rightOp: Expr<FpType>) = FpMaxExpr(leftOp, rightOp)

  @JvmStatic fun Min(leftOp: Expr<FpType>, rightOp: Expr<FpType>) = FpMinExpr(leftOp, rightOp)

  @JvmStatic
  fun ToBv(roundingMode: FpRoundingMode, op: Expr<FpType>, size: Int, sgn: Boolean) =
    FpToBvExpr(roundingMode, op, size, sgn)

  @JvmStatic
  fun ToFp(roundingMode: FpRoundingMode, op: Expr<FpType>, exp: Int, sig: Int) =
    FpToFpExpr(roundingMode, op, exp, sig)
}
