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
package hu.bme.mit.theta.core.type.inttype

import hu.bme.mit.theta.core.type.Expr
import java.math.BigInteger

/** Factory and utility methods for integer expressions. */
@Suppress("FunctionName")
object IntExprs {
  @JvmStatic fun Int() = IntType

  @JvmStatic fun Int(value: Int) = IntLitExpr(BigInteger.valueOf(value.toLong()))

  @JvmStatic fun Int(value: String) = IntLitExpr(BigInteger(value))

  @JvmStatic fun Int(value: BigInteger) = IntLitExpr(value)

  @JvmStatic fun ToRat(op: Expr<IntType>) = IntToRatExpr(op)

  @JvmStatic fun Add(ops: Iterable<Expr<IntType>>) = IntAddExpr.of(ops)

  @JvmStatic @SafeVarargs fun Add(vararg ops: Expr<IntType>) = IntAddExpr(ops.asList())

  @JvmStatic fun Sub(leftOp: Expr<IntType>, rightOp: Expr<IntType>) = IntSubExpr(leftOp, rightOp)

  @JvmStatic fun Pos(op: Expr<IntType>) = IntPosExpr(op)

  @JvmStatic fun Neg(op: Expr<IntType>) = IntNegExpr(op)

  @JvmStatic fun Mul(ops: Iterable<Expr<IntType>>) = IntMulExpr.of(ops)

  @JvmStatic @SafeVarargs fun Mul(vararg ops: Expr<IntType>) = IntMulExpr(ops.asList())

  @JvmStatic fun Div(leftOp: Expr<IntType>, rightOp: Expr<IntType>) = IntDivExpr(leftOp, rightOp)

  @JvmStatic fun Mod(leftOp: Expr<IntType>, rightOp: Expr<IntType>) = IntModExpr(leftOp, rightOp)

  @JvmStatic fun Rem(leftOp: Expr<IntType>, rightOp: Expr<IntType>) = IntRemExpr(leftOp, rightOp)

  @JvmStatic fun Eq(leftOp: Expr<IntType>, rightOp: Expr<IntType>) = IntEqExpr(leftOp, rightOp)

  @JvmStatic fun Neq(leftOp: Expr<IntType>, rightOp: Expr<IntType>) = IntNeqExpr(leftOp, rightOp)

  @JvmStatic fun Lt(leftOp: Expr<IntType>, rightOp: Expr<IntType>) = IntLtExpr(leftOp, rightOp)

  @JvmStatic fun Leq(leftOp: Expr<IntType>, rightOp: Expr<IntType>) = IntLeqExpr(leftOp, rightOp)

  @JvmStatic fun Gt(leftOp: Expr<IntType>, rightOp: Expr<IntType>) = IntGtExpr(leftOp, rightOp)

  @JvmStatic fun Geq(leftOp: Expr<IntType>, rightOp: Expr<IntType>) = IntGeqExpr(leftOp, rightOp)
}
