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

import hu.bme.mit.theta.core.decl.ParamDecl
import hu.bme.mit.theta.core.type.Expr

/** Factory and utility methods for boolean expressions. */
@Suppress("FunctionName")
object BoolExprs {

  @JvmStatic fun Bool() = BoolType

  @JvmStatic fun Bool(value: Boolean) = BoolLitExpr.of(value)

  @JvmStatic fun True() = TrueExpr

  @JvmStatic fun False() = FalseExpr

  @JvmStatic fun Not(op: Expr<BoolType>) = NotExpr(op)

  @JvmStatic fun Imply(leftOp: Expr<BoolType>, rightOp: Expr<BoolType>) = ImplyExpr(leftOp, rightOp)

  @JvmStatic fun Iff(leftOp: Expr<BoolType>, rightOp: Expr<BoolType>) = IffExpr(leftOp, rightOp)

  @JvmStatic fun Xor(leftOp: Expr<BoolType>, rightOp: Expr<BoolType>) = XorExpr(leftOp, rightOp)

  @JvmStatic fun And(ops: Iterable<Expr<BoolType>>) = AndExpr.of(ops)

  @JvmStatic fun Or(ops: Iterable<Expr<BoolType>>) = OrExpr.of(ops)

  @JvmStatic
  fun Forall(paramDecls: Iterable<ParamDecl<*>>, op: Expr<BoolType>) = ForallExpr.of(paramDecls, op)

  @JvmStatic
  fun Exists(paramDecls: Iterable<ParamDecl<*>>, op: Expr<BoolType>) = ExistsExpr.of(paramDecls, op)

  // Convenience methods
  @JvmStatic @SafeVarargs fun And(vararg ops: Expr<BoolType>) = AndExpr.of(ops.asList())

  @JvmStatic @SafeVarargs fun Or(vararg ops: Expr<BoolType>) = OrExpr.of(ops.asList())
}
