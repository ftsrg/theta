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

class LinearBlockDecompositionTest {

  @Test
  fun `straight-line procedure decomposes into a single block`() {
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
    blockGraph.checkConsistency()

    assertEquals(1, blockGraph.blocks.size)
    val onlyBlock = blockGraph.blocks.single()
    assertEquals(procedure.initLoc, onlyBlock.initialLocation)
    assertTrue(onlyBlock.finalLocation.final)
    assertTrue(onlyBlock.isRoot)
    assertTrue(onlyBlock.successorIds.isEmpty())
  }

  @Test
  fun `a branch that merges back decomposes into three blocks`() {
    val procedure =
      xcfa("if-else") {
          procedure("main") {
            "x" type Int()
            (init to "branch") { "x" assign "0" }
            ("branch" to "thenLoc") { assume("(< x 10)") }
            ("branch" to "elseLoc") { assume("(>= x 10)") }
            ("thenLoc" to final) { "x" assign "(+ x 1)" }
            ("elseLoc" to final) { "x" assign "(+ x 2)" }
          }
        }
        .procedures
        .single()

    val blockGraph = LinearBlockDecomposition().decompose(procedure)
    blockGraph.checkConsistency()

    assertEquals(3, blockGraph.blocks.size)

    val root = blockGraph.root
    assertEquals(procedure.initLoc, root.initialLocation)
    assertEquals("branch", root.finalLocation.name)

    val arms = blockGraph.successorsOf(root)
    assertEquals(2, arms.size)
    arms.forEach { arm ->
      assertEquals("branch", arm.initialLocation.name)
      assertTrue(arm.finalLocation.final)
      assertTrue(arm.successorIds.isEmpty())
    }
  }

  @Test
  fun `paper's x-y while-loop example decomposes with the loop body as its own block`() {
    val procedure =
      xcfa("xy-loop") {
          procedure("main") {
            "x" type Int()
            "y" type Int()
            (init to "loophead") {
              "x" assign "0"
              "y" assign "0"
            }
            ("loophead" to "body") { assume("(< x 10)") }
            ("loophead" to "afterloop") { assume("(>= x 10)") }
            ("body" to "loophead") {
              "x" assign "(+ x 1)"
              "y" assign "(+ y 1)"
            }
            ("afterloop" to final) { assume("(= x y)") }
            ("afterloop" to err) { assume("(/= x y)") }
          }
        }
        .procedures
        .single()

    val blockGraph = LinearBlockDecomposition().decompose(procedure)
    blockGraph.checkConsistency()

    assertEquals(5, blockGraph.blocks.size)

    val root = blockGraph.root
    assertEquals(procedure.initLoc, root.initialLocation)
    assertEquals("loophead", root.finalLocation.name)

    val loopHeadSuccessors = blockGraph.successorsOf(root)
    assertEquals(2, loopHeadSuccessors.size)

    val loopBody = loopHeadSuccessors.single { it.finalLocation.name == "loophead" }
    assertEquals("loophead", loopBody.initialLocation.name)
    assertEquals(setOf("loophead", "body"), loopBody.locations.map { it.name }.toSet())
    assertTrue(loopBody.id in loopBody.predecessorIds)
    assertTrue(loopBody.id in loopBody.successorIds)

    val loopExit = loopHeadSuccessors.single { it.finalLocation.name == "afterloop" }
    val exitSuccessors = blockGraph.successorsOf(loopExit)
    assertEquals(2, exitSuccessors.size)
    assertTrue(exitSuccessors.any { it.finalLocation.final })
    assertTrue(exitSuccessors.any { it.finalLocation.error })
    exitSuccessors.forEach { assertTrue(it.successorIds.isEmpty()) }
  }

  @Test
  fun `a three-way branch that merges back produces one block per arm`() {
    val procedure =
      xcfa("three-way-branch") {
          procedure("main") {
            "x" type Int()
            (init to "branch") { "x" assign "0" }
            ("branch" to "arm1") { assume("(< x 1)") }
            ("branch" to "arm2") { assume("(< x 2)") }
            ("branch" to "arm3") { assume("(< x 3)") }
            ("arm1" to "join") { "x" assign "1" }
            ("arm2" to "join") { "x" assign "2" }
            ("arm3" to "join") { "x" assign "3" }
            ("join" to final) { nop() }
          }
        }
        .procedures
        .single()

    val blockGraph = LinearBlockDecomposition().decompose(procedure)
    blockGraph.checkConsistency()

    assertEquals(5, blockGraph.blocks.size)

    val root = blockGraph.root
    assertEquals("branch", root.finalLocation.name)

    val arms = blockGraph.successorsOf(root)
    assertEquals(3, arms.size)
    val joinBlock =
      arms
        .map { blockGraph.successorsOf(it) }
        .also { successorSets -> successorSets.forEach { assertEquals(1, it.size) } }
        .flatten()
        .toSet()
        .single()
    assertEquals(3, joinBlock.predecessorIds.size)
    assertTrue(joinBlock.finalLocation.final)
  }

  @Test
  fun `an outer and an inner loop each get their own loop-head block`() {
    val procedure =
      xcfa("nested-loop") {
          procedure("main") {
            "x" type Int()
            (init to "outerHead") { "x" assign "0" }
            ("outerHead" to "innerHead") { assume("(< x 10)") }
            ("outerHead" to "afterOuter") { assume("(>= x 10)") }
            ("innerHead" to "innerBody") { assume("(< x 5)") }
            ("innerHead" to "outerHead") { assume("(>= x 5)") }
            ("innerBody" to "innerHead") { "x" assign "(+ x 1)" }
            ("afterOuter" to final) { nop() }
          }
        }
        .procedures
        .single()

    val blockGraph = LinearBlockDecomposition().decompose(procedure)
    blockGraph.checkConsistency()

    assertEquals(5, blockGraph.blocks.size)

    val selfLoopingBlocks = blockGraph.blocks.filter { it.id in it.successorIds }
    assertEquals(1, selfLoopingBlocks.size)
    val innerBodyBlock = selfLoopingBlocks.single()
    assertEquals("innerHead", innerBodyBlock.initialLocation.name)
    assertEquals("innerHead", innerBodyBlock.finalLocation.name)
    assertEquals(setOf("innerHead", "innerBody"), innerBodyBlock.locations.map { it.name }.toSet())

    assertEquals(2, blockGraph.blocks.count { it.finalLocation.name == "outerHead" })
    assertEquals(2, blockGraph.blocks.count { it.finalLocation.name == "innerHead" })
    val innerHeadToOuterHead =
      blockGraph.blocks.single {
        it.initialLocation.name == "innerHead" && it.finalLocation.name == "outerHead"
      }
    assertEquals(2, blockGraph.predecessorsOf(innerHeadToOuterHead).size)
  }

  @Test
  fun `a break out of a loop body creates a branch point inside the body`() {
    val procedure =
      xcfa("loop-with-break") {
          procedure("main") {
            "x" type Int()
            (init to "loopHead") { "x" assign "0" }
            ("loopHead" to "body1") { assume("(< x 10)") }
            ("loopHead" to "after") { assume("(>= x 10)") }
            ("body1" to "body2") { assume("(< x 5)") }
            ("body1" to "after") { assume("(>= x 5)") } // break: bypasses the loop head
            ("body2" to "loopHead") { "x" assign "(+ x 1)" }
            ("after" to final) { nop() }
          }
        }
        .procedures
        .single()

    val blockGraph = LinearBlockDecomposition().decompose(procedure)
    blockGraph.checkConsistency()

    assertEquals(6, blockGraph.blocks.size)

    val body1Block = blockGraph.blocks.single { it.finalLocation.name == "body1" }
    val body1Successors = blockGraph.successorsOf(body1Block)
    assertEquals(2, body1Successors.size)
    assertTrue(body1Successors.any { it.finalLocation.name == "loopHead" })
    assertTrue(body1Successors.any { it.finalLocation.name == "after" })

    val afterBlock = blockGraph.blocks.single { it.initialLocation.name == "after" }
    assertEquals(2, afterBlock.predecessorIds.size)
  }

  @Test
  fun `locations unreachable from the initial location are excluded`() {
    val procedure =
      xcfa("dead-code") {
          procedure("main") {
            "x" type Int()
            (init to "L0") { "x" assign "0" }
            ("L0" to final) { "x" assign "(+ x 1)" }
            ("deadCode" to "alsoDeadCode") { "x" assign "42" }
          }
        }
        .procedures
        .single()

    val blockGraph = LinearBlockDecomposition().decompose(procedure)
    blockGraph.checkConsistency()

    assertEquals(1, blockGraph.blocks.size)
    val coveredNames = blockGraph.blocks.flatMap { it.locations }.map { it.name }.toSet()
    assertTrue("deadCode" !in coveredNames)
    assertTrue("alsoDeadCode" !in coveredNames)
  }

  @Test
  fun `parallel edges between the same two locations become distinct blocks`() {
    val procedure =
      xcfa("parallel-edges") {
          procedure("main") {
            "x" type Int()
            (init to "A") { "x" assign "0" }
            ("A" to "B") { "x" assign "1" }
            ("A" to "B") { "x" assign "2" }
            ("B" to final) { nop() }
          }
        }
        .procedures
        .single()

    val blockGraph = LinearBlockDecomposition().decompose(procedure)
    blockGraph.checkConsistency()

    assertEquals(4, blockGraph.blocks.size)

    val root = blockGraph.root
    val parallelArms = blockGraph.successorsOf(root)
    assertEquals(2, parallelArms.size)
    parallelArms.forEach { arm ->
      assertEquals("A", arm.initialLocation.name)
      assertEquals("B", arm.finalLocation.name)
    }
    assertEquals(2, parallelArms.map { it.edges }.toSet().size)
  }

  @Test
  fun `a tight self-loop with an empty body is its own single-location block`() {
    val procedure =
      xcfa("tight-self-loop") {
          procedure("main") {
            (init to "loopHead") { nop() }
            ("loopHead" to "loopHead") { nop() }
            ("loopHead" to "after") { nop() }
            ("after" to final) { nop() }
          }
        }
        .procedures
        .single()

    val blockGraph = LinearBlockDecomposition().decompose(procedure)
    blockGraph.checkConsistency()

    assertEquals(3, blockGraph.blocks.size)

    val selfLoopBlock = blockGraph.blocks.single { it.id in it.successorIds }
    assertEquals("loopHead", selfLoopBlock.initialLocation.name)
    assertEquals("loopHead", selfLoopBlock.finalLocation.name)
    assertEquals(setOf("loopHead"), selfLoopBlock.locations.map { it.name }.toSet())
    assertEquals(1, selfLoopBlock.edges.size)
  }

  @Test
  fun `a custom isBlockEnd predicate is honored, splitting every edge into its own block`() {
    val procedure =
      xcfa("custom-predicate") {
          procedure("main") {
            "x" type Int()
            (init to "A") { "x" assign "0" }
            ("A" to "B") { "x" assign "(+ x 1)" }
            ("B" to final) { "x" assign "(+ x 1)" }
          }
        }
        .procedures
        .single()

    val everyLocationIsABlockEnd = LinearBlockDecomposition { true }
    val blockGraph = everyLocationIsABlockEnd.decompose(procedure)
    blockGraph.checkConsistency()

    assertEquals(3, blockGraph.blocks.size)
    assertTrue(blockGraph.blocks.all { it.edges.size == 1 })

    val root = blockGraph.root
    val middle = blockGraph.successorsOf(root).single()
    val last = blockGraph.successorsOf(middle).single()
    assertTrue(last.successorIds.isEmpty())
    assertTrue(last.finalLocation.final)
  }
}
