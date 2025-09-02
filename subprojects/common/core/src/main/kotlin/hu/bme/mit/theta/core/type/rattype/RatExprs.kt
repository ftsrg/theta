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
package hu.bme.mit.theta.core.type.rattype

import hu.bme.mit.theta.core.type.Expr
import java.math.BigInteger

/** Factory for rational expressions. */
@Suppress("FunctionName")
object RatExprs {
  @JvmStatic fun Rat() = RatType

  @JvmStatic
  fun Rat(num: Int, denom: Int) =
    RatLitExpr.of(BigInteger.valueOf(num.toLong()), BigInteger.valueOf(denom.toLong()))

  @JvmStatic
  fun Rat(num: Int, denom: String) =
    RatLitExpr.of(BigInteger.valueOf(num.toLong()), BigInteger(denom))

  @JvmStatic
  fun Rat(num: Int, denom: BigInteger) = RatLitExpr.of(BigInteger.valueOf(num.toLong()), denom)

  @JvmStatic
  fun Rat(num: String, denom: Int) =
    RatLitExpr.of(BigInteger(num), BigInteger.valueOf(denom.toLong()))

  @JvmStatic fun Rat(num: String, denom: String) = RatLitExpr.of(BigInteger(num), BigInteger(denom))

  @JvmStatic fun Rat(num: String, denom: BigInteger) = RatLitExpr.of(BigInteger(num), denom)

  @JvmStatic
  fun Rat(num: BigInteger, denom: Int) = RatLitExpr.of(num, BigInteger.valueOf(denom.toLong()))

  @JvmStatic fun Rat(num: BigInteger, denom: String) = RatLitExpr.of(num, BigInteger(denom))

  @JvmStatic fun Rat(num: BigInteger, denom: BigInteger) = RatLitExpr.of(num, denom)

  @JvmStatic fun Add(ops: Iterable<Expr<RatType>>) = RatAddExpr.of(ops)

  @JvmStatic fun Sub(leftOp: Expr<RatType>, rightOp: Expr<RatType>) = RatSubExpr(leftOp, rightOp)

  @JvmStatic fun Pos(op: Expr<RatType>) = RatPosExpr(op)

  @JvmStatic fun Neg(op: Expr<RatType>) = RatNegExpr(op)

  @JvmStatic fun Mul(ops: Iterable<Expr<RatType>>) = RatMulExpr.of(ops)

  @JvmStatic fun Div(leftOp: Expr<RatType>, rightOp: Expr<RatType>) = RatDivExpr(leftOp, rightOp)

  @JvmStatic fun Eq(leftOp: Expr<RatType>, rightOp: Expr<RatType>) = RatEqExpr(leftOp, rightOp)

  @JvmStatic fun Neq(leftOp: Expr<RatType>, rightOp: Expr<RatType>) = RatNeqExpr(leftOp, rightOp)

  @JvmStatic fun Lt(leftOp: Expr<RatType>, rightOp: Expr<RatType>) = RatLtExpr(leftOp, rightOp)

  @JvmStatic fun Leq(leftOp: Expr<RatType>, rightOp: Expr<RatType>) = RatLeqExpr(leftOp, rightOp)

  @JvmStatic fun Gt(leftOp: Expr<RatType>, rightOp: Expr<RatType>) = RatGtExpr(leftOp, rightOp)

  @JvmStatic fun Geq(leftOp: Expr<RatType>, rightOp: Expr<RatType>) = RatGeqExpr(leftOp, rightOp)

  @JvmStatic @SafeVarargs fun Add(vararg ops: Expr<RatType>) = RatAddExpr(ops.asList())

  @JvmStatic @SafeVarargs fun Mul(vararg ops: Expr<RatType>) = RatMulExpr(ops.asList())

  @JvmStatic fun ToInt(op: Expr<RatType>) = RatToIntExpr.of(op)
}
