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
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import kotlinx.serialization.Serializable
import kotlinx.serialization.Transient

@Serializable
class IteExpr<ExprType : Type>
private constructor(
  val cond: Expr<BoolType>,
  val then: Expr<ExprType>,
  val `else`: Expr<ExprType>,
) : Expr<ExprType> {

  @Transient @Volatile private var hashCode = 0

  override val ops: List<Expr<*>>
    get() = ImmutableList.of(cond, then, `else`)

  override val arity: Int
    get() = 3

  override val type: ExprType
    get() = then.type

  override fun eval(valuation: Valuation): LitExpr<ExprType> {
    val condVal = cond.eval(valuation) as BoolLitExpr
    return if (condVal.value) then.eval(valuation) else `else`.eval(valuation)
  }

  override fun withOps(ops: List<Expr<*>>): IteExpr<ExprType> {
    checkArgument(ops.size == 3)
    val exprType = type
    return with(cast(ops[0], Bool()), cast(ops[1], exprType), cast(ops[2], exprType))
  }

  fun with(cond: Expr<BoolType>, then: Expr<ExprType>, elze: Expr<ExprType>): IteExpr<ExprType> =
    if (this.cond === cond && this.then === then && this.`else` === elze) this
    else of(cond, then, elze)

  fun withCond(cond: Expr<BoolType>): IteExpr<ExprType> = with(cond, then, `else`)

  fun withThen(then: Expr<ExprType>): IteExpr<ExprType> = with(cond, then, `else`)

  fun withElse(elze: Expr<ExprType>): IteExpr<ExprType> = with(cond, then, elze)

  override fun hashCode(): Int {
    var result = hashCode
    if (result == 0) {
      result = HASH_SEED
      result = 31 * result + cond.hashCode()
      result = 31 * result + then.hashCode()
      result = 31 * result + `else`.hashCode()
      hashCode = result
    }
    return result
  }

  override fun equals(other: Any?): Boolean {
    if (other is TraceableWrapperExpr<*>) return equals(other.expr)
    if (this === other) return true
    if (other == null || javaClass != other.javaClass) return false
    val that = other as IteExpr<*>
    return cond == that.cond && then == that.then && `else` == that.`else`
  }

  override fun toString(): String =
    Utils.lispStringBuilder(OPERATOR_LABEL).body().add(cond).add(then).add(`else`).toString()

  companion object {
    private const val HASH_SEED = 181
    private const val OPERATOR_LABEL = "ite"

    @JvmStatic
    fun <ExprType : Type> of(
      cond: Expr<BoolType>,
      then: Expr<ExprType>,
      elze: Expr<ExprType>,
    ): IteExpr<ExprType> = IteExpr(cond, then, elze)

    @JvmStatic
    fun <ExprType : Type> create(cond: Expr<*>, then: Expr<*>, elze: Expr<*>): IteExpr<*> {
      @Suppress("UNCHECKED_CAST") val newThen = then as Expr<ExprType>
      return of(cast(cond, Bool()), newThen, cast(elze, newThen.type))
    }
  }
}
