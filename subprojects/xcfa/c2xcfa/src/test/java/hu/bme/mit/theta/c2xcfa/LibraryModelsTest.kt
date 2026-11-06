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
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.model.InvokeLabel
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.utils.getAllLabels
import java.math.BigInteger
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertFalse
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

/** The library models, and which of their values [XCFA.overApproximatedVars] records. */
class LibraryModelsTest {

  /** Builds `library-models/[name]` from the test resources. */
  private fun build(name: String): XCFA =
    getXcfaFromC(
        javaClass.getResourceAsStream("/library-models/$name")!!,
        ParseContext(),
        false,
        XcfaProperty(ErrorDetection.OVERFLOW),
        NullLogger.getInstance(),
      )
      .first

  private fun XCFA.recorded(prefix: String) =
    overApproximatedVars.filterKeys { it.name.startsWith(prefix) }

  private fun XCFA.calls(name: String) =
    procedures
      .flatMap { p -> p.edges.flatMap { it.getAllLabels() } }
      .count { it is InvokeLabel && it.name == name }

  private fun XCFA.hasVar(prefix: String) =
    procedures.any { p -> p.vars.any { it.name.startsWith(prefix) } }

  @Test
  fun `strerror gives a fresh string whose characters are recorded`() {
    val xcfa = build("strerror.c")
    assertEquals(0, xcfa.calls("strerror"))
    assertEquals(127, xcfa.recorded("__stub_strerror_").size)
  }

  @Test
  fun `strlen is exact and not recorded when no stub writes a buffer`() {
    val xcfa = build("strlen-exact.c")
    assertTrue(xcfa.hasVar("__theta_strlen_index_var_"))
    assertTrue(xcfa.recorded("call_strlen_ret").isEmpty())
  }

  @Test
  fun `strlen stays a recorded stub when a stub writes a buffer`() {
    val xcfa = build("strlen-after-buffer-stub.c")
    assertFalse(xcfa.hasVar("__theta_strlen_index_var_"))
    assertFalse(xcfa.recorded("call_strlen_ret").isEmpty())
  }

  @Test
  fun `the return of snprintf is bounded by its format literals`() {
    val xcfa = build("snprintf-bound.c")
    val bounds = xcfa.recorded("call_snprintf_ret").values
    assertEquals(listOf(BigInteger.valueOf(22)), bounds.map { it?.endInclusive })
  }
}
