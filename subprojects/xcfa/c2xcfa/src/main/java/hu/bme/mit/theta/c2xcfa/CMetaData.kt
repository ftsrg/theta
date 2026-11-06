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

import hu.bme.mit.theta.frontend.SourcePosition
import hu.bme.mit.theta.frontend.transformation.model.statements.CStatement
import hu.bme.mit.theta.xcfa.model.*

data class CMetaData(
  val lineNumberStart: Int?,
  val colNumberStart: Int?,
  val lineNumberStop: Int?,
  val colNumberStop: Int?,
  val offsetStart: Int?,
  val offsetEnd: Int?,
  val sourceText: String?,
  val astNodes: List<CStatement>,
  val functionName: String?,
  // we only want to export metadata when we encounter the fist label for a statement
  val notStatementStart: Boolean = false,
  // start of the innermost C full expression of the label, null if unknown; see [targetPosition]
  val fullExpression: SourcePosition? = null,
) : MetaData() {

  private data class Position(val line: Int, val col: Int, val offset: Int?)

  private fun startPosition(): Position? =
    lineNumberStart?.takeIf { it > 0 }?.let { Position(it, colNumberStart ?: 0, offsetStart) }

  private fun stopPosition(): Position? =
    lineNumberStop?.takeIf { it > 0 }?.let { Position(it, colNumberStop ?: 0, offsetEnd) }

  // AST nodes must be in order of combination!
  override fun combine(other: MetaData): MetaData =
    when (other) {
      is CMetaData -> {
        // line, column and offset of one end belong together, so each end comes from one side
        val order = compareBy<Position>({ it.line }, { it.col })
        val start = listOfNotNull(startPosition(), other.startPosition()).minWithOrNull(order)
        val stop = listOfNotNull(stopPosition(), other.stopPosition()).maxWithOrNull(order)
        CMetaData(
          lineNumberStart = start?.line ?: 0,
          colNumberStart = start?.col?.takeIf { it > 0 } ?: 0,
          offsetStart = start?.offset?.takeIf { it > 0 } ?: 0,
          lineNumberStop = stop?.line ?: 0,
          colNumberStop = stop?.col?.takeIf { it > 0 } ?: 0,
          offsetEnd = stop?.offset?.takeIf { it > 0 } ?: 0,
          sourceText = (sourceText ?: "") + (other.sourceText ?: ""),
          astNodes = astNodes + other.astNodes,
          functionName = functionName ?: other.functionName,
          fullExpression = fullExpression ?: other.fullExpression,
        )
      }

      is EmptyMetaData -> this

      else ->
        error(
          "Cannot combine metadata of different types or different function names: $this vs $other"
        )
    }

  /**
   * Where a violation in this label is located: the start of its innermost full expression, else of
   * its statement, or null if neither is known. Unlike exported positions, this is also known for a
   * label that does not start its statement.
   */
  val targetPosition: SourcePosition?
    get() =
      fullExpression
        ?: lineNumberStart
          ?.takeIf { it > 0 }
          ?.let { line -> colNumberStart?.let { SourcePosition(line, it) } }

  override fun isSubstantial(): Boolean {
    if (astNodes.isEmpty()) {
      return false
    }
    if (lineNumberStart == null || lineNumberStop == null) {
      return false
    }
    if (lineNumberStart < 0 || lineNumberStop < 0) {
      return false
    }
    if (colNumberStart == null || colNumberStop == null) {
      return false
    }
    if (colNumberStart < 0 || colNumberStop < 0) {
      return false
    }
    if (notStatementStart) {
      return false
    }
    return true
  }

  val asExportableCMetadata: CMetaData? = if (notStatementStart) null else this
}

fun XcfaLabel.getCMetaData(): CMetaData? = (metadata as? CMetaData)?.asExportableCMetadata

fun XcfaLocation.getCMetaData(): CMetaData? = (metadata as? CMetaData)?.asExportableCMetadata

fun XcfaEdge.getCMetaData(): CMetaData? = (metadata as? CMetaData)?.asExportableCMetadata

fun MetaData.targetPosition(): SourcePosition? = (this as? CMetaData)?.targetPosition
