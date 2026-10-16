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
package hu.bme.mit.theta.xcfa.dss.analysis

import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.core.type.inttype.IntExprs.*
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.xcfa.cli.checkers.getCegarChecker
import hu.bme.mit.theta.xcfa.cli.params.defaultPredicateCegarConfig
import hu.bme.mit.theta.xcfa.cli.utils.ensureDefaultSolversRegistered
import hu.bme.mit.theta.xcfa.model.*
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.BeforeAll
import org.junit.jupiter.api.Test

/**
 * Build-order step 3: with `NO_DECOMPOSITION`, a DSS worker is a plain call into Theta's
 * config-driven CEGAR, so it must report exactly what calling that entry point directly would.
 */
class WorkerConfigDelegatorTest {

  companion object {

    @JvmStatic
    @BeforeAll
    fun registerSolvers() {
      ensureDefaultSolversRegistered(defaultPredicateCegarConfig(), NullLogger.getInstance())
    }
  }

  private fun cegarChecker(xcfa: XCFA) =
    getCegarChecker(
      xcfa,
      emptySet(),
      ParseContext(),
      defaultPredicateCegarConfig(),
      NullLogger.getInstance(),
    )

  private fun safeXcfa() =
    xcfa("safe") {
      val main =
        procedure("main") {
          "x" type Int()
          (init to final) { "x" assign "0" }
        }
      main.start()
    }

  private fun unsafeXcfa() =
    xcfa("unsafe") {
      val main =
        procedure("main") {
          "x" type Int()
          (init to err) { "x" assign "0" }
        }
      main.start()
    }

  @Test
  fun `reports SAFE for a program that never reaches the error location`() {
    val xcfa = safeXcfa()
    val result = runWorkerConfig(xcfa, checkerFactory = { x -> cegarChecker(x) })
    assertTrue(result.isSafe)
  }

  @Test
  fun `reports UNSAFE for a program that reaches the error location`() {
    val xcfa = unsafeXcfa()
    val result = runWorkerConfig(xcfa, checkerFactory = { x -> cegarChecker(x) })
    assertTrue(result.isUnsafe)
  }

  @Test
  fun `reproduces exactly what a direct getCegarChecker invocation would report`() {
    for (xcfa in listOf(safeXcfa(), unsafeXcfa())) {
      val direct = cegarChecker(xcfa).check()
      val delegated = runWorkerConfig(xcfa, checkerFactory = { x -> cegarChecker(x) })

      assertEquals(direct.isSafe, delegated.isSafe)
      assertEquals(direct.isUnsafe, delegated.isUnsafe)
    }
  }
}
