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
package hu.bme.mit.theta.xcfa.cli.dss.actor

import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.inttype.IntExprs.*
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.xcfa.analysis.XcfaPrec
import hu.bme.mit.theta.xcfa.analysis.dss.actor.*
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.DssCheckerRoster
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.XcfaChecker
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.collectPreds
import hu.bme.mit.theta.xcfa.analysis.dss.decomposition.SingleBlockDecomposition
import hu.bme.mit.theta.xcfa.cli.checkers.getCegarChecker
import hu.bme.mit.theta.xcfa.cli.dss.ensureDefaultSolversRegistered
import hu.bme.mit.theta.xcfa.cli.params.getDefaultPredCegarConfig
import hu.bme.mit.theta.xcfa.model.*
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.BeforeAll
import org.junit.jupiter.api.Test

/** `--dss-reuse-block-precision`: a block's later runs start with what its earlier runs learned. */
class ReuseBlockPrecisionTest {

  companion object {

    @JvmStatic
    @BeforeAll
    fun registerSolvers() {
      ensureDefaultSolversRegistered(getDefaultPredCegarConfig(), NullLogger.getInstance())
    }
  }

  /** havoc x; y := x; y > x is unreachable, but CEGAR needs a refinement to see that. */
  private val program: XCFA =
    xcfa("reuse-precision") {
      val main =
        procedure("main") {
          "x" type Int()
          "y" type Int()
          (init to "a") { havoc("x") }
          ("a" to "b") { "y" assign "x" }
          ("b" to err) { assume("(> y x)") }
          ("b" to final) { assume("(<= y x)") }
        }
      main.start()
    }

  private class Recorded {
    val initial = mutableListOf<Set<Expr<BoolType>>>()
    val last = mutableListOf<Set<Expr<BoolType>>>()
  }

  private fun recordingRoster(recorded: Recorded) =
    DssCheckerRoster(
      listOf { x ->
        val inner =
          getCegarChecker(
            x,
            emptySet(),
            ParseContext(),
            getDefaultPredCegarConfig(),
            NullLogger.getInstance(),
          )
        object : XcfaChecker by inner {
          override fun check(input: XcfaPrec<*>?) =
            inner.check(input).also { record(input?.collectPreds().orEmpty(), it) }

          override fun check() = inner.check().also { record(emptySet(), it) }

          private fun record(initial: Set<Expr<BoolType>>, result: SafetyResult<*, *>) {
            recorded.initial += initial
            recorded.last += (result.prec.orElse(null) as? XcfaPrec<*>)?.collectPreds().orEmpty()
          }
        }
      }
    )

  private fun analyzeTwice(reuseBlockPrecision: Boolean): Recorded {
    val recorded = Recorded()
    val procedure = program.procedures.single()
    val behavior =
      PredicateBlockBehavior(
        program,
        procedure,
        SingleBlockDecomposition.decompose(procedure).blocks.single(),
        recordingRoster(recorded),
        useGlobalPredicatePool = false,
        reuseBlockPrecision = reuseBlockPrecision,
      )
    behavior.runInitialAnalysis()
    behavior.runInitialAnalysis()
    return recorded
  }

  @Test
  fun `the second run starts with the predicates the first run ended with`() {
    val recorded = analyzeTwice(reuseBlockPrecision = true)
    assertEquals(2, recorded.initial.size)
    assertTrue(recorded.initial[0].isEmpty()) { "first run: ${recorded.initial[0]}" }
    assertTrue(recorded.last[0].isNotEmpty()) { "the first run should have refined" }
    assertTrue(recorded.initial[1].containsAll(recorded.last[0])) {
      "second run started with ${recorded.initial[1]}, first ended with ${recorded.last[0]}"
    }
  }

  @Test
  fun `without the flag every run starts from scratch`() {
    val recorded = analyzeTwice(reuseBlockPrecision = false)
    assertEquals(2, recorded.initial.size)
    assertTrue(recorded.last[0].isNotEmpty()) { "the first run should have refined" }
    assertTrue(recorded.initial[1].isEmpty()) { "second run: ${recorded.initial[1]}" }
  }
}
