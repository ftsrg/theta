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
package hu.bme.mit.theta.core.stmt

import hu.bme.mit.theta.common.Utils
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

/**
 * Non-deterministic statement of the form `nondet { STMT1, STMT2, ... }`. The statement executes
 * exactly one of the given statements, chosen non-deterministically.
 */
@Serializable
@SerialName(NonDetStmt.STMT_LABEL)
data class NonDetStmt(val stmts: List<Stmt>) : Stmt {

  init {
    check(stmts.isNotEmpty())
  }

  companion object {

    internal const val STMT_LABEL = "nondet"

    @JvmStatic
    fun of(stmts: List<Stmt>): NonDetStmt {
      val stmtList = stmts.ifEmpty { listOf(SkipStmt) }
      return NonDetStmt(stmtList)
    }
  }

  override fun <P, R> accept(visitor: StmtVisitor<P, R>, param: P): R = visitor.visit(this, param)

  override fun toString(): String = Utils.lispStringBuilder(STMT_LABEL).addAll(stmts).toString()
}
