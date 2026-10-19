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
package hu.bme.mit.theta.frontend.transformation.model.statements

import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.frontend.ParseContext
import java.util.Collections

class CCompound(parseContext: ParseContext) : CStatement(parseContext) {
  private val cStatementList: MutableList<CStatement> = ArrayList()

  /** Unmodifiable list of statements */
  fun getcStatementList(): List<CStatement> = Collections.unmodifiableList(cStatementList)

  fun insertCStatementsToFront(cStatements: List<CStatement>) {
    cStatementList.addAll(0, cStatements)
    cStatementList.forEach { it.setParent(this) }
  }

  fun addCStatement(cStatement: CStatement) {
    cStatementList.add(cStatement)
    cStatement.setParent(this)
  }

  override val expression: Expr<*>?
    get() = cStatementList[cStatementList.size - 1].expression

  override var preStatements: CStatement? = null
    set(value) {
      field = value
      value?.setParent(this)
    }

  override var postStatements: CStatement? = null
    set(value) {
      field = value
      value?.setParent(this)
    }

  override fun <P, R> accept(visitor: CStatementVisitor<P, R>, param: P): R =
    visitor.visit(this, param)
}
