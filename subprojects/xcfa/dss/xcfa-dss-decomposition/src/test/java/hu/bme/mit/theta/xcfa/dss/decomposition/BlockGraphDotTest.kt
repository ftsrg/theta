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
package hu.bme.mit.theta.xcfa.dss.decomposition

import hu.bme.mit.theta.core.type.inttype.IntExprs.*
import hu.bme.mit.theta.xcfa.model.*
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

class BlockGraphDotTest {

  @Test
  fun `renders every block as a node and every successor relation as an edge`() {
    val procedure =
      xcfa("branch") {
          procedure("main") {
            "x" type Int()
            (init to "branch") { "x" assign "0" }
            ("branch" to final) { assume("(< x 10)") }
            ("branch" to err) { assume("(>= x 10)") }
          }
        }
        .procedures
        .single()

    val blockGraph = LinearBlockDecomposition().decompose(procedure)
    val dot = blockGraph.toDot()

    assertTrue(dot.startsWith("digraph BlockGraph {\n"))
    assertTrue(dot.trimEnd().endsWith("}"))
    for (block in blockGraph.blocks) {
      assertTrue(dot.contains("\"${block.id}\""), "missing node for ${block.id} in:\n$dot")
      for (successorId in block.successorIds) {
        assertTrue(
          dot.contains("\"${block.id}\" -> \"${successorId}\";"),
          "missing edge ${block.id} -> $successorId in:\n$dot",
        )
      }
    }
  }

  @Test
  fun `the root block is rendered with a double border`() {
    val procedure =
      xcfa("straight-line") {
          procedure("main") {
            "x" type Int()
            (init to "L0") { "x" assign "0" }
            ("L0" to final) { "x" assign "(+ x 1)" }
          }
        }
        .procedures
        .single()

    val blockGraph = LinearBlockDecomposition().decompose(procedure)
    val dot = blockGraph.toDot()

    assertEquals(1, blockGraph.blocks.size)
    val root = blockGraph.root
    assertTrue(root.isRoot)
    val nodeLine = dot.lines().single { it.trim().startsWith("\"${root.id}\"") }
    assertTrue(nodeLine.contains("peripheries=2"), "expected a double border in: $nodeLine")
  }

  @Test
  fun `a block with a dedicated abstraction point is rendered with a dashed border`() {
    val procedure =
      xcfa("branch") {
          procedure("main") {
            "x" type Int()
            (init to "branch") { "x" assign "0" }
            ("branch" to "afterA") { assume("(< x 10)") }
            ("branch" to "afterB") { assume("(>= x 10)") }
            ("afterA" to final) { nop() }
            ("afterB" to err) { nop() }
          }
        }
        .procedures
        .single()

    val blockGraph = LinearBlockDecomposition().decompose(procedure)
    val instrumented = BlockGraphInstrumentation.instrumentForAbstraction(procedure, blockGraph)
    val dot = instrumented.blockGraph.toDot()

    // "branch" (root's own finalLocation) has two outgoing edges, so root - not either arm, both
    // of which dead-end straight into final/err - is the one block that gets a ghost edge.
    val instrumentedBlock = instrumented.blockGraph.root
    assertTrue(instrumentedBlock.isAbstractionPossible)
    val nodeLine =
      dot.lines().single {
        it.trim().startsWith("\"${instrumentedBlock.id}\"") && it.contains("label=")
      }
    assertTrue(nodeLine.contains("style=dashed"), "expected a dashed border in: $nodeLine")
    assertTrue(
      nodeLine.contains("vcond: ${instrumentedBlock.violationConditionLocation.name}"),
      "expected the vcond location name in the label: $nodeLine",
    )
  }

  @Test
  fun `a cyclic block (its own predecessor and successor) renders a self-loop edge`() {
    val procedure =
      xcfa("xy-loop") {
          procedure("main") {
            "x" type Int()
            (init to "loophead") { "x" assign "0" }
            ("loophead" to "body") { assume("(< x 10)") }
            ("loophead" to "afterloop") { assume("(>= x 10)") }
            ("body" to "loophead") { "x" assign "(+ x 1)" }
            ("afterloop" to final) { nop() }
          }
        }
        .procedures
        .single()

    val blockGraph = LinearBlockDecomposition().decompose(procedure)
    val dot = blockGraph.toDot()

    val loopBody = blockGraph.blocks.single { it.id in it.predecessorIds }
    assertTrue(
      dot.contains("\"${loopBody.id}\" -> \"${loopBody.id}\";"),
      "expected a self-loop edge for ${loopBody.id} in:\n$dot",
    )
  }
}
