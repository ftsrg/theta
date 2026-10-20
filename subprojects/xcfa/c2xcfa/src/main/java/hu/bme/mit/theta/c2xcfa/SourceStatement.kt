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
package hu.bme.mit.theta.c2xcfa

import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.frontend.transformation.model.statements.CCall
import hu.bme.mit.theta.frontend.transformation.model.statements.CDoWhile
import hu.bme.mit.theta.frontend.transformation.model.statements.CFor
import hu.bme.mit.theta.frontend.transformation.model.statements.CIf
import hu.bme.mit.theta.frontend.transformation.model.statements.CStatement
import hu.bme.mit.theta.frontend.transformation.model.statements.CWhile
import java.util.IdentityHashMap
import kotlinx.serialization.Serializable

/**
 * What witness handling reads of a C statement a label came from: its kind and span, and for a call
 * the callee and its result variable. Equal facts mean the same statement ([id]). Columns are
 * 0-based.
 */
@Serializable
data class SourceStatement(
  val id: Int,
  val kind: Kind,
  val lineNumberStart: Int,
  val colNumberStart: Int,
  val lineNumberStop: Int,
  val colNumberStop: Int,
  val call: Call? = null,
) {

  enum class Kind {
    CALL,
    IF,
    WHILE,
    FOR,
    DO_WHILE,
    OTHER;

    val isBranching: Boolean
      get() = this == IF || this == WHILE || this == FOR || this == DO_WHILE
  }

  /** [openParenColumn] is the column of the call's `(`, if that is on the call's first line. */
  @Serializable
  data class Call(val functionId: String, val ret: VarDecl<*>, val openParenColumn: Int?)

  /** Gives each statement one fact; facts of different statements differ in their [id]. */
  class Registry {
    private val facts = IdentityHashMap<CStatement, SourceStatement>()

    fun of(statement: CStatement): SourceStatement =
      facts.getOrPut(statement) {
        SourceStatement(
          id = facts.size,
          kind =
            when (statement) {
              is CCall -> Kind.CALL
              is CIf -> Kind.IF
              is CWhile -> Kind.WHILE
              is CFor -> Kind.FOR
              is CDoWhile -> Kind.DO_WHILE
              else -> Kind.OTHER
            },
          lineNumberStart = statement.lineNumberStart,
          colNumberStart = statement.colNumberStart,
          lineNumberStop = statement.lineNumberStop,
          colNumberStop = statement.colNumberStop,
          call =
            (statement as? CCall)?.let {
              Call(it.functionId, it.ret, openParenColumn(it.sourceText, it.colNumberStart))
            },
        )
      }

    private fun openParenColumn(text: String, colStart: Int): Int? {
      val paren = text.indexOf('(')
      return if (colStart < 0 || paren < 0 || text.substring(0, paren).contains('\n')) null
      else colStart + paren
    }
  }
}
