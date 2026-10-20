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
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import kotlinx.serialization.Serializable
import kotlinx.serialization.Transient

/**
 * Assignment statement of the form VARIABLE := EXPRESSION. The statement updates the VARIABLE with
 * the result of EXPRESSION.
 */
@Serializable
class AssignStmt<DeclType : Type>
private constructor(val varDecl: VarDecl<DeclType>, val expr: Expr<DeclType>) : Stmt {

  @Transient @Volatile private var hashCode = 0

  override fun <P, R> accept(visitor: StmtVisitor<in P, out R>, param: P): R =
    visitor.visit(this, param)

  override fun hashCode(): Int {
    var result = hashCode
    if (result == 0) {
      result = HASH_SEED
      result = 31 * result + varDecl.hashCode()
      result = 31 * result + expr.hashCode()
      hashCode = result
    }
    return result
  }

  override fun equals(other: Any?): Boolean =
    if (this === other) true
    else if (other != null && javaClass == other.javaClass) {
      val that = other as AssignStmt<*>
      varDecl == that.varDecl && expr == that.expr
    } else false

  override fun toString(): String =
    Utils.lispStringBuilder(STMT_LABEL).add(varDecl.name).add(expr).toString()

  companion object {
    private const val HASH_SEED = 409
    private const val STMT_LABEL = "assign"

    @JvmStatic
    fun <DeclType : Type> of(lhs: VarDecl<DeclType>, rhs: Expr<DeclType>): AssignStmt<DeclType> =
      AssignStmt(lhs, rhs)

    @JvmStatic
    fun <DeclType : Type> create(lhs: VarDecl<*>, rhs: Expr<*>): AssignStmt<*> {
      @Suppress("UNCHECKED_CAST") val newLhs = lhs as VarDecl<DeclType>
      val newRhs: Expr<DeclType> = cast(rhs, newLhs.type)
      return of(newLhs, newRhs)
    }
  }
}
