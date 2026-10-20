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
package hu.bme.mit.theta.core.stmt

import hu.bme.mit.theta.common.Utils
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import kotlinx.serialization.Serializable
import kotlinx.serialization.Transient

/**
 * Assume statement of the form [EXPRESSION], where EXPRESSION is a Boolean [Expr]. The statement is
 * a guard that can only be passed if EXPRESSION evaluates to true.
 */
@Serializable
class AssumeStmt private constructor(val cond: Expr<BoolType>) : Stmt {

  @Transient @Volatile private var hashCode = 0

  override fun <P, R> accept(visitor: StmtVisitor<in P, out R>, param: P): R =
    visitor.visit(this, param)

  override fun hashCode(): Int {
    var result = hashCode
    if (result == 0) {
      result = HASH_SEED
      result = 31 * result + cond.hashCode()
      hashCode = result
    }
    return result
  }

  override fun equals(other: Any?): Boolean =
    if (this === other) true
    else if (other != null && javaClass == other.javaClass) {
      val that = other as AssumeStmt
      cond == that.cond
    } else false

  override fun toString(): String = Utils.lispStringBuilder(STMT_LABEL).add(cond).toString()

  companion object {
    private const val HASH_SEED = 547
    private const val STMT_LABEL = "assume"

    @JvmStatic fun of(cond: Expr<BoolType>): AssumeStmt = AssumeStmt(cond)

    @JvmStatic fun create(cond: Expr<*>): AssumeStmt = of(cast(cond, Bool()))
  }
}
