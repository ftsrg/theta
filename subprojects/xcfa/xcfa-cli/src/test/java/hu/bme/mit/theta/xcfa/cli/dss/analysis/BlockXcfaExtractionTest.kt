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
package hu.bme.mit.theta.xcfa.cli.dss.analysis

import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.core.type.inttype.IntExprs.*
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.*
import hu.bme.mit.theta.xcfa.analysis.dss.decomposition.Block
import hu.bme.mit.theta.xcfa.analysis.dss.decomposition.LinearBlockDecomposition
import hu.bme.mit.theta.xcfa.cli.checkers.getCegarChecker
import hu.bme.mit.theta.xcfa.cli.dss.ensureDefaultSolversRegistered
import hu.bme.mit.theta.xcfa.cli.params.getDefaultPredCegarConfig
import hu.bme.mit.theta.xcfa.model.*
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.BeforeAll
import org.junit.jupiter.api.Test

class BlockXcfaExtractionTest {

  companion object {

    @JvmStatic
    @BeforeAll
    fun registerSolvers() {
      ensureDefaultSolversRegistered(getDefaultPredCegarConfig(), NullLogger.getInstance())
    }
  }

  private fun branchingProcedureXcfa(): XCFA =
    xcfa("block-extraction") {
      val main =
        procedure("main") {
          "x" type Int()
          (init to "branch") { "x" assign "0" }
          ("branch" to "safeArm") { assume("(< x 10)") }
          ("branch" to "unsafeArm") { assume("(>= x 10)") }
          ("safeArm" to final) { "x" assign "(+ x 1)" }
          ("unsafeArm" to err) { "x" assign "(+ x 2)" }
        }
      main.start()
    }

  private fun branchingProcedure() = branchingProcedureXcfa().procedures.single()

  private fun check(xcfa: XCFA) = runWorkerConfig(xcfa, checkerFactory = { x -> cegarChecker(x) })

  private fun cegarChecker(xcfa: XCFA) =
    getCegarChecker(
      xcfa,
      emptySet(),
      ParseContext(),
      getDefaultPredCegarConfig(),
      NullLogger.getInstance(),
    )

  @Test
  fun `a block with no error location checks as SAFE in isolation`() {
    val procedure = branchingProcedure()
    val blockGraph = LinearBlockDecomposition().decompose(procedure)
    val safeArmBlock = blockGraph.blocks.single { it.locations.any { l -> l.name == "safeArm" } }

    val result = check(extractBlockXcfa(procedure, safeArmBlock).xcfa)

    assertTrue(result.isSafe)
  }

  @Test
  fun `cloned locations do not carry adjacency from outside the block`() {
    val procedure = branchingProcedure()
    val blockGraph = LinearBlockDecomposition().decompose(procedure)
    val safeArmBlock = blockGraph.blocks.single { it.locations.any { l -> l.name == "safeArm" } }

    val extracted = extractBlockXcfa(procedure, safeArmBlock)
    val branch = extracted.xcfa.procedures.single().locs.single { it.name == "branch" }

    assertEquals(setOf("safeArm"), branch.outgoingEdges.map { it.target.name }.toSet())
  }

  @Test
  fun `a block that reaches the error location checks as UNSAFE in isolation, even from the block's own most-general entry state`() {
    val procedure = branchingProcedure()
    val blockGraph = LinearBlockDecomposition().decompose(procedure)
    val unsafeArmBlock =
      blockGraph.blocks.single { it.locations.any { l -> l.name == "unsafeArm" } }
    assertEquals("branch", unsafeArmBlock.initialLocation.name)

    val result = check(extractBlockXcfa(procedure, unsafeArmBlock).xcfa)

    assertTrue(result.isUnsafe)
  }

  @Test
  fun `the root block, which never reaches an error location on its own, checks as SAFE`() {
    val procedure = branchingProcedure()
    val blockGraph = LinearBlockDecomposition().decompose(procedure)

    val result = check(extractBlockXcfa(procedure, blockGraph.root).xcfa)

    assertTrue(result.isSafe)
  }

  @Test
  fun `extracting the whole procedure as a single block reproduces the same verdict as checking it directly`() {
    val procedure = branchingProcedure()
    val wholeProcedureAsABlock =
      Block(
        id = "whole",
        initialLocation = procedure.initLoc,
        finalLocation = procedure.finalLoc.orElseThrow(),
        locations = procedure.locs,
        edges = procedure.edges,
      )

    val direct = check(branchingProcedureXcfa())
    val extracted = check(extractBlockXcfa(procedure, wholeProcedureAsABlock).xcfa)

    assertTrue(direct.isSafe)
    assertEquals(direct.isSafe, extracted.isSafe)
    assertEquals(direct.isUnsafe, extracted.isUnsafe)
  }
}
