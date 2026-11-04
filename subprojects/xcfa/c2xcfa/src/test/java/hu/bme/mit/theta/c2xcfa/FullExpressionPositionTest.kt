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

import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.SourcePosition
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.model.XcfaLabel
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

/**
 * Labels know the start of the C full expression they evaluate, where witnesses put targets. The
 * expected positions are the code that the `// <kind>: <code>` comments of the program point at.
 */
class FullExpressionPositionTest {

  private val source = javaClass.getResource("/full-expression.c")!!.readText()

  private val labels: List<XcfaLabel> by lazy {
    val (xcfa, _, _) =
      getXcfaFromC(
        source.byteInputStream(),
        ParseContext(),
        false,
        XcfaProperty(ErrorDetection.ERROR_LOCATION),
        NullLogger.getInstance(),
      )
    xcfa.procedures.flatMap { it.edges }.flatMap { it.label.getFlatLabels() }
  }

  private fun marked(kind: String): List<SourcePosition> =
    source.lines().mapIndexedNotNull { index, line ->
      line
        .substringAfter("// $kind: ", "")
        .takeIf { it.isNotEmpty() }
        ?.let { code -> SourcePosition(index + 1, line.indexOf(code)) }
    }

  @Test
  fun testLabelsCarryTheirFullExpression() {
    val positions = labels.mapNotNull { it.metadata.targetPosition() }.toSet()
    val expected = marked("full expression")
    assertTrue(expected.isNotEmpty())
    for (position in expected) {
      assertTrue(position in positions) { "No label at $position, only at $positions" }
    }
  }

  @Test
  fun testCombinedPositionsComeFromOneSide() {
    val (first, second) =
      marked("statement").map { position ->
        labels
          .map { it.metadata }
          .filterIsInstance<CMetaData>()
          .firstOrNull {
            it.lineNumberStart == position.line && it.colNumberStart == position.column
          } ?: error("No label starts at $position")
      }
    // the earlier statement starts in a later column, so mixing both sides gives a wrong start
    assertTrue(first.colNumberStart!! > second.colNumberStart!!)
    val combined = first.combine(second) as CMetaData
    assertEquals(
      first.lineNumberStart to first.colNumberStart,
      combined.lineNumberStart to combined.colNumberStart,
    )
    assertEquals(
      second.lineNumberStop to second.colNumberStop,
      combined.lineNumberStop to combined.colNumberStop,
    )
  }
}
