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
import hu.bme.mit.theta.core.type.inttype.IntType

class LoopStmt
private constructor(
  val stmt: Stmt,
  val loopVariable: VarDecl<IntType>,
  val from: Expr<IntType>,
  val to: Expr<IntType>,
) : Stmt {

  @Volatile private var hashCode = 0

  override fun <P, R> accept(visitor: StmtVisitor<in P, out R>, param: P): R =
    visitor.visit(this, param)

  override fun hashCode(): Int {
    var result = hashCode
    if (result == 0) {
      result = HASH_SEED
      result =
        37 * result + stmt.hashCode() + loopVariable.hashCode() + from.hashCode() + to.hashCode()
      hashCode = result
    }
    return result
  }

  override fun equals(other: Any?): Boolean =
    if (this === other) true
    else if (other != null && javaClass == other.javaClass) {
      val that = other as LoopStmt
      stmt == that.stmt && loopVariable == that.loopVariable && from == that.from && to == that.to
    } else false

  override fun toString(): String =
    Utils.lispStringBuilder(STMT_LABEL).add("$loopVariable from $from to $to $stmt").toString()

  companion object {
    private const val HASH_SEED = 361
    private const val STMT_LABEL = "loop"

    @JvmStatic
    fun of(
      stmt: Stmt,
      loopVariable: VarDecl<IntType>,
      from: Expr<IntType>,
      to: Expr<IntType>,
    ): LoopStmt = LoopStmt(stmt, loopVariable, from, to)
  }
}
