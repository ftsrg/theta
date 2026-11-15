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
package hu.bme.mit.theta.xcfa.analysis

import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.algorithm.bounded.BoundedChecker
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.c2xcfa.getXcfaFromC
import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.analysis.monolithic.BlockEncoding
import hu.bme.mit.theta.xcfa.analysis.monolithic.XcfaPipelineChecker
import hu.bme.mit.theta.xcfa.analysis.proof.LocationInvariants
import hu.bme.mit.theta.xcfa.model.NondetLabel
import hu.bme.mit.theta.xcfa.model.StmtLabel
import hu.bme.mit.theta.xcfa.utils.getAllLabels
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.assertThrows

/** A bounded engine with block encoding counts loop iterations, not edges. */
class BlockEncodingTest {

  private fun check(
    file: String,
    blockEncoding: Boolean,
    maxBound: Int,
  ): SafetyResult<LocationInvariants, Trace<XcfaState<PtrState<ExplState>>, XcfaAction>> {
    val parseContext = ParseContext()
    val property = XcfaProperty(ErrorDetection.ERROR_LOCATION)
    val xcfa =
      getXcfaFromC(
          javaClass.getResourceAsStream("/c/block-encoding/$file")!!,
          parseContext,
          false,
          property,
          NullLogger.getInstance(),
        )
        .first
    val factory = Z3LegacySolverFactory.getInstance()
    return XcfaPipelineChecker(
        xcfa,
        property,
        parseContext,
        { monolithicExpr ->
          BoundedChecker(
            monolithicExpr = monolithicExpr,
            shouldGiveUp = { it > maxBound },
            bmcSolver = factory.createSolver(),
            indSolver = factory.createSolver(),
            logger = NullLogger.getInstance(),
          )
        },
        acceptUnreliableSafe = false,
        blockEncoding = blockEncoding,
      )
      .check()
  }

  @Test
  fun kInductionClosesAfterFewBlocks() {
    assertTrue(check("loop_safe.c", blockEncoding = true, maxBound = 3).isSafe)
    assertTrue(
      check("loop_safe.c", blockEncoding = false, maxBound = 3).let { !it.isSafe && !it.isUnsafe }
    )
  }

  @Test
  fun aLoopFreeProgramIsOneBlock() {
    assertTrue(check("loop_free_safe.c", blockEncoding = true, maxBound = 2).isSafe)
    assertTrue(
      check("loop_free_safe.c", blockEncoding = false, maxBound = 2).let {
        !it.isSafe && !it.isUnsafe
      }
    )
  }

  @Test
  fun aCallAfterTheLastErrorPathIsNotDropped() {
    assertThrows<IllegalArgumentException> {
      check("longjmp.c", blockEncoding = true, maxBound = 5)
    }
    assertThrows<IllegalArgumentException> {
      check("longjmp.c", blockEncoding = false, maxBound = 5)
    }
  }

  @Test
  fun aCounterexampleHasTheOriginalLabels() {
    val result = check("loop_unsafe.c", blockEncoding = true, maxBound = 5)
    assertTrue(result.isUnsafe)
    val labels = result.asUnsafe().cex.actions.flatMap { it.label.getAllLabels() }
    assertTrue(labels.none { it is NondetLabel })
    assertTrue(labels.none { BlockEncoding.CHOICE_PREFIX in it.toString() })
  }

  @Test
  fun aCounterexampleGivesTheValuesOfItsHavocs() {
    val result = check("loop_unsafe.c", blockEncoding = true, maxBound = 5)
    assertTrue(result.isUnsafe)
    val cex = result.asUnsafe().cex as HintedTrace<*>
    cex.actions.forEachIndexed { i, action ->
      val havocs = action.label.getFlatLabels().count { it is StmtLabel && it.stmt is HavocStmt<*> }
      assertEquals(havocs, cex.inputs[i].size)
    }
    assertTrue(cex.inputs.any { inputs -> inputs.any { it != null } })
  }
}
