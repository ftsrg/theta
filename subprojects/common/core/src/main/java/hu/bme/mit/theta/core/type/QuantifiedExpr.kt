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

import com.google.common.base.Preconditions.checkArgument
import com.google.common.collect.ImmutableList
import hu.bme.mit.theta.common.Utils
import hu.bme.mit.theta.core.decl.ParamDecl
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.TypeUtils

sealed class QuantifiedExpr : Expr<BoolType> {

  abstract val paramDecls: List<ParamDecl<*>>
  abstract val op: Expr<BoolType>

  @Volatile private var hashCode = 0

  final override val type: BoolType
    get() = Bool()

  override val ops: List<Expr<BoolType>>
    get() = ImmutableList.of(op)

  override fun withOps(ops: List<Expr<*>>): Expr<BoolType> {
    checkArgument(ops.size == 1)
    return with(TypeUtils.cast(ops[0], Bool()))
  }

  override val arity: Int
    get() = 1

  final override fun hashCode(): Int {
    var result = hashCode
    if (result == 0) {
      result = hashSeed
      result = 31 * result + paramDecls.hashCode()
      result = 31 * result + op.hashCode()
      hashCode = result
    }
    return result
  }

  override fun equals(other: Any?): Boolean {
    if (other is TraceableWrapperExpr<*>) return equals(other.expr)
    if (this === other) return true
    if (other == null || javaClass != other.javaClass) return false
    val that = other as QuantifiedExpr
    return paramDecls == that.paramDecls && op == that.op
  }

  final override fun toString(): String {
    val paramString = paramDecls.joinToString(" ", "(", ")") { "(${it.name} ${it.type})" }
    return Utils.lispStringBuilder(operatorLabel).body().add(paramString).add(op).toString()
  }

  abstract fun with(op: Expr<BoolType>): QuantifiedExpr

  protected abstract val hashSeed: Int

  abstract val operatorLabel: String
}
