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
package hu.bme.mit.theta.xcfa.cli

import hu.bme.mit.theta.analysis.EmptyCex
import hu.bme.mit.theta.analysis.algorithm.EmptyProof
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.xcfa.cli.params.ErrorCodeException
import hu.bme.mit.theta.xcfa.cli.params.ExitCodes
import hu.bme.mit.theta.xcfa.cli.params.SpecBackendConfig
import hu.bme.mit.theta.xcfa.cli.params.SpecFrontendConfig
import hu.bme.mit.theta.xcfa.cli.params.XcfaConfig
import hu.bme.mit.theta.xcfa.cli.portfolio.ConfigNode
import hu.bme.mit.theta.xcfa.cli.portfolio.STM
import hu.bme.mit.theta.xcfa.cli.portfolio.chainEdges
import hu.bme.mit.theta.xcfa.cli.portfolio.step
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertThrows
import org.junit.jupiter.api.Test

class ChainEdgesTest {

  private val config = XcfaConfig<SpecFrontendConfig, SpecBackendConfig>()
  private val safe = SafetyResult.safe<EmptyProof, EmptyCex>(EmptyProof.getInstance())

  /** Configurations named `<algorithm>-<solver>` that fail with the code given for their name. */
  private fun chain(failures: Map<String, ExitCodes>, vararg solvers: Pair<String, String>): STM {
    val make = { name: String ->
      { _: Long, solver: String ->
        ConfigNode("$name-$solver", config) {
          failures["$name-$solver"]?.let { throw ErrorCodeException(it.code) } ?: safe
        }
      }
    }
    val steps = solvers.mapIndexed { i, (solver, alt) -> step(make("step$i"), 0, solver, alt) }
    val last = make("last")(0, "s")
    return STM(steps.first().first, chainEdges(steps, last, inProcess = true))
  }

  private fun solvedBy(stm: STM) =
    ((stm.execute(NullLogger.getInstance()).first as Pair<*, *>).first)

  @Test
  fun `a solver error moves the step to its twin`() {
    val stm = chain(mapOf("step0-a" to ExitCodes.SOLVER_ERROR), "a" to "b", "a" to "b")
    assertEquals("step0-b", solvedBy(stm))
  }

  @Test
  fun `a solver error on the twin moves on to the next step`() {
    val failures = mapOf("step0-a" to ExitCodes.SOLVER_ERROR, "step0-b" to ExitCodes.SOLVER_ERROR)
    assertEquals("step1-a", solvedBy(chain(failures, "a" to "b", "a" to "b")))
  }

  @Test
  fun `a step without an alternative solver moves on after a solver error`() {
    val stm = chain(mapOf("step0-a" to ExitCodes.SOLVER_ERROR), "a" to "a", "a" to "b")
    assertEquals("step1-a", solvedBy(stm))
  }

  @Test
  fun `a timeout skips the twin`() {
    val stm = chain(mapOf("step0-a" to ExitCodes.TIMEOUT), "a" to "b", "a" to "b")
    assertEquals("step1-a", solvedBy(stm))
  }

  @Test
  fun `a server error still leaves the in-process chain`() {
    val stm = chain(mapOf("step0-a" to ExitCodes.SERVER_ERROR), "a" to "b")
    val e = assertThrows(ErrorCodeException::class.java) { solvedBy(stm) }
    assertEquals(ExitCodes.SERVER_ERROR.code, e.code)
  }
}
