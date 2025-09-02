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

import hu.bme.mit.theta.common.Utils
import hu.bme.mit.theta.core.decl.ParamDecl
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

/** Abstract base class for quantified boolean expressions (forall, exists). */
@Serializable
sealed class QuantifiedExpr : Expr<BoolType> {

  abstract val paramDecls: List<ParamDecl<*>>
  abstract val op: Expr<BoolType>

  override val type: BoolType = Bool()
  override val ops: List<Expr<*>>
    get() = listOf(op)

  override fun withOps(ops: List<Expr<*>>): Expr<BoolType> {
    require(ops.size == 1) { "QuantifiedExpr expects exactly one operand." }
    return with(cast(ops[0], Bool()))
  }

  override fun eval(`val`: Valuation): LitExpr<BoolType> = throw UnsupportedOperationException()

  override fun toString(): String {
    val paramString =
      paramDecls.joinToString(" ", prefix = "(", postfix = ")") { "(${it.name} ${it.type})" }
    return Utils.lispStringBuilder(operatorLabel).body().add(paramString).add(op).toString()
  }

  abstract fun with(op: Expr<BoolType>): QuantifiedExpr

  protected abstract val operatorLabel: String
}

/** Existential quantifier expression for boolean type. */
@Serializable
@SerialName("Exists")
data class ExistsExpr(
  override val paramDecls: List<ParamDecl<*>>,
  override val op: Expr<BoolType>,
) : QuantifiedExpr() {

  companion object {

    private const val OPERATOR_LABEL = "exists"

    @JvmStatic
    fun of(paramDecls: Iterable<ParamDecl<*>>, op: Expr<BoolType>) =
      ExistsExpr(paramDecls.toList(), op)

    @JvmStatic
    fun create(paramDecls: Iterable<ParamDecl<*>>, op: Expr<*>) =
      ExistsExpr(paramDecls.toList(), cast(op, Bool()))
  }

  override fun with(op: Expr<BoolType>): ExistsExpr =
    if (op == this.op) this else ExistsExpr(paramDecls, op)

  override val operatorLabel: String = OPERATOR_LABEL

  override fun toString(): String = super.toString()
}

/** Universal quantifier expression for boolean type. */
@Serializable
@SerialName("Forall")
data class ForallExpr(
  override val paramDecls: List<ParamDecl<*>>,
  override val op: Expr<BoolType>,
) : QuantifiedExpr() {

  companion object {

    private const val OPERATOR_LABEL = "forall"

    @JvmStatic
    fun of(paramDecls: Iterable<ParamDecl<*>>, op: Expr<BoolType>) =
      ForallExpr(paramDecls.toList(), op)

    @JvmStatic
    fun create(paramDecls: Iterable<ParamDecl<*>>, op: Expr<*>) =
      ForallExpr(paramDecls.toList(), cast(op, Bool()))
  }

  override fun with(op: Expr<BoolType>): ForallExpr =
    if (op == this.op) this else ForallExpr(paramDecls, op)

  override val operatorLabel: String = OPERATOR_LABEL

  override fun toString(): String = super.toString()
}
