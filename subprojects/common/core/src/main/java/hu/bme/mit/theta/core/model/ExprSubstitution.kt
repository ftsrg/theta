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
package hu.bme.mit.theta.core.model

import com.google.common.base.Preconditions
import hu.bme.mit.theta.common.Utils
import hu.bme.mit.theta.common.container.Containers
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import java.util.*
import kotlin.concurrent.Volatile

/** Interface for a substitution, which is a mapping from expressions to expressions. */
interface ExprSubstitution {

  /**
   * Get all the expressions for which an expression is assigned.
   *
   * @return
   */
  val mappedExprs: MutableCollection<out Expr<*>>

  /**
   * Evaluate an expression, i.e., get the corresponding expression.
   *
   * @param decl
   * @param <ExprType>
   * @return </ExprType>
   */
  fun <ExprType : Type> eval(expr: Expr<ExprType>): Optional<out Expr<ExprType>>

  fun <T : Type> apply(expr: Expr<T>): Expr<T> {
    if (mappedExprs.contains(expr)) {
      val optSub = eval(expr)
      if (optSub.isPresent) {
        val sub: Expr<T> = optSub.get()
        return sub
      } else {
        return expr
      }
    } else {
      return expr.map { this.apply(it) }
    }
  }
}

/** Basic, immutable implementation of an expr to expr substitution. */
class BasicExprSubstitution private constructor(builder: Builder) : ExprSubstitution {

  @Volatile private var hashCode = 0

  override val mappedExprs: MutableCollection<Expr<*>> =
    Containers.createSet(builder.exprToExpr.keys)
  private val exprToExpr: MutableMap<Expr<*>, Expr<*>> = builder.exprToExpr

  override fun <ExprType : Type> eval(expr: Expr<ExprType>): Optional<Expr<ExprType>> {
    Preconditions.checkNotNull(expr)
    if (exprToExpr.containsKey(expr)) {
      val `val` = exprToExpr[expr] as Expr<ExprType>
      return Optional.of(`val`)
    }
    return Optional.empty()
  }

  override fun toString(): String {
    return Utils.lispStringBuilder("ExprSubstitution")
      .addAll(exprToExpr.entries.map { it.key.toString() + " <- " + it })
      .toString()
  }

  override fun equals(other: Any?): Boolean {
    if (this === other) {
      return true
    } else if (other != null && this.javaClass == other.javaClass) {
      val that = other as BasicExprSubstitution
      return this.exprToExpr == that.exprToExpr
    } else {
      return false
    }
  }

  override fun hashCode(): Int {
    var result = hashCode
    if (result == 0) {
      result = HASH_SEED
      result = 31 * result + exprToExpr.hashCode()
      hashCode = result
    }
    return result
  }

  class Builder(val exprToExpr: MutableMap<Expr<*>, Expr<*>> = Containers.createMap()) {

    private var built = false

    fun put(key: Expr<*>, value: Expr<*>): Builder {
      Preconditions.checkState(!built, "Builder was already built.")
      Preconditions.checkArgument(value.getType() == key.getType(), "Type mismatch.")
      exprToExpr[key] = value
      return this
    }

    fun putAll(declToExpr: MutableMap<Expr<*>, Expr<*>>): Builder {
      Preconditions.checkState(!built, "Builder was already built.")
      declToExpr.entries.forEach { put(it.key, it.value) }
      return this
    }

    fun build(): ExprSubstitution {
      built = true
      return BasicExprSubstitution(this)
    }
  }

  companion object {

    private const val HASH_SEED = 2521
  }
}
