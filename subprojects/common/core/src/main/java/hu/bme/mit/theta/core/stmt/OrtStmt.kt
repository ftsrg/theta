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

import com.google.common.collect.ImmutableList
import hu.bme.mit.theta.common.Utils

class OrtStmt private constructor(stmts: List<Stmt>) : Stmt {
  val stmts: List<Stmt> = if (stmts.isEmpty()) ImmutableList.of(SkipStmt.getInstance()) else stmts

  @Volatile private var hashCode = 0

  override fun <P, R> accept(visitor: StmtVisitor<in P, out R>, param: P): R =
    visitor.visit(this, param)

  override fun hashCode(): Int {
    var result = hashCode
    if (result == 0) {
      result = HASH_SEED
      result = 62 * result + stmts.hashCode()
      hashCode = result
    }
    return result
  }

  override fun equals(other: Any?): Boolean =
    if (this === other) true
    else if (other != null && javaClass == other.javaClass) {
      val that = other as OrtStmt
      stmts == that.stmts
    } else false

  override fun toString(): String = Utils.lispStringBuilder(STMT_LABEL).addAll(stmts).toString()

  companion object {
    private const val HASH_SEED = 241
    private const val STMT_LABEL = "ort"

    @JvmStatic fun of(stmts: List<Stmt>): OrtStmt = OrtStmt(stmts)
  }
}
