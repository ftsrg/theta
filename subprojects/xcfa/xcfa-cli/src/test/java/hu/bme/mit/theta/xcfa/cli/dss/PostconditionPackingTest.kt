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
package hu.bme.mit.theta.xcfa.cli.dss

import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.False
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.inttype.IntExprs.*
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.xcfa.analysis.XcfaPrec
import hu.bme.mit.theta.xcfa.analysis.dss.*
import hu.bme.mit.theta.xcfa.analysis.dss.decomposition.Block
import hu.bme.mit.theta.xcfa.analysis.dss.decomposition.LinearBlockDecomposition
import hu.bme.mit.theta.xcfa.cli.checkers.getCegarChecker
import hu.bme.mit.theta.xcfa.cli.params.getDefaultPredCegarConfig
import hu.bme.mit.theta.xcfa.model.*
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.BeforeAll
import org.junit.jupiter.api.Test

class PostconditionPackingTest {

  companion object {

    @JvmStatic
    @BeforeAll
    fun registerSolvers() {
      ensureDefaultSolversRegistered(getDefaultPredCegarConfig(), NullLogger.getInstance())
    }
  }

  private fun xcfa5Xcfa(): XCFA =
    xcfa("postcondition-packing") {
      val main =
        procedure("main") {
          "x" type Int()
          (init to "branch") { "x" assign "5" }
          ("branch" to "checkA") { assume("(< x 10)") }
          ("branch" to "checkB") { assume("(>= x 10)") }
          ("checkA" to final) { nop() }
          ("checkB" to err) { nop() }
        }
      main.start()
    }

  private fun xcfa5Procedure() = xcfa5Xcfa().procedures.single()

  private fun check(xcfa: XCFA, precision: XcfaPrec<*>? = null) =
    runWorkerConfig(xcfa, checkerFactory = { x -> cegarChecker(x) }, initialPrecision = precision)

  private fun cegarChecker(xcfa: XCFA) =
    getCegarChecker(
      xcfa,
      emptySet(),
      ParseContext(),
      getDefaultPredCegarConfig(),
      NullLogger.getInstance(),
    )

  /** Checks [block] and packs the postcondition it produces at [Block.finalLocation]. */
  private fun postconditionAtExit(
    wholeProgram: XCFA,
    procedure: XcfaProcedure,
    block: Block,
    precondition: Expr<BoolType>? = null,
  ): Expr<BoolType> {
    val extraction = extractBlockXcfa(procedure, block, precondition = precondition)
    val result = check(extraction.xcfa, getAssumePredPrec(wholeProgram))
    check(result.isSafe) { "Expected $block to check as safe, but got: $result" }
    return packPostcondition(result, extraction.locationMapping.getValue(block.finalLocation))
  }

  @Test
  fun `the non-decomposed baseline is SAFE (checkB's error location is unreachable)`() {
    assertTrue(check(xcfa5Xcfa()).isSafe)
  }

  @Test
  fun `checking checkB from its own top entry alone is spuriously UNSAFE`() {
    val procedure = xcfa5Procedure()
    val blockGraph = LinearBlockDecomposition().decompose(procedure)
    val checkBBlock = blockGraph.blocks.single { it.locations.any { l -> l.name == "checkB" } }

    val result = check(extractBlockXcfa(procedure, checkBBlock).xcfa)

    assertTrue(result.isUnsafe)
  }

  @Test
  fun `feeding checkB the real packed postcondition from its predecessor gives the correct SAFE result`() {
    val wholeProgram = xcfa5Xcfa()
    val procedure = wholeProgram.procedures.single()
    val blockGraph = LinearBlockDecomposition().decompose(procedure)
    val root = blockGraph.root
    val checkBBlock = blockGraph.blocks.single { it.locations.any { l -> l.name == "checkB" } }

    val postcondition = postconditionAtExit(wholeProgram, procedure, root)
    assertTrue(postcondition != True())

    val checkBExtraction = extractBlockXcfa(procedure, checkBBlock, precondition = postcondition)
    val checkBResult = check(checkBExtraction.xcfa, getAssumePredPrec(wholeProgram))

    assertTrue(checkBResult.isSafe)
  }

  @Test
  fun `a postcondition packed for a location nothing reached is False`() {
    val wholeProgram = xcfa5Xcfa()
    val procedure = wholeProgram.procedures.single()
    val blockGraph = LinearBlockDecomposition().decompose(procedure)
    val root = blockGraph.root
    val checkBBlock = blockGraph.blocks.single { it.locations.any { l -> l.name == "checkB" } }

    val postcondition = postconditionAtExit(wholeProgram, procedure, root)
    val checkBExtraction = extractBlockXcfa(procedure, checkBBlock, precondition = postcondition)
    val checkBResult = check(checkBExtraction.xcfa, getAssumePredPrec(wholeProgram))
    assertTrue(checkBResult.isSafe)
    val checkBLocation =
      checkBExtraction.locationMapping.getValue(
        checkBBlock.locations.single { it.name == "checkB" }
      )

    assertEquals(False(), packPostcondition(checkBResult, checkBLocation))
  }
}
