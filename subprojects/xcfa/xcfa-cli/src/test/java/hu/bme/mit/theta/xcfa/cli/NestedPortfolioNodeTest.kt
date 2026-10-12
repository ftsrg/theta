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
import hu.bme.mit.theta.xcfa.cli.params.SpecBackendConfig
import hu.bme.mit.theta.xcfa.cli.params.SpecFrontendConfig
import hu.bme.mit.theta.xcfa.cli.params.XcfaConfig
import hu.bme.mit.theta.xcfa.cli.portfolio.ConfigNode
import hu.bme.mit.theta.xcfa.cli.portfolio.Edge
import hu.bme.mit.theta.xcfa.cli.portfolio.NestedPortfolioNode
import hu.bme.mit.theta.xcfa.cli.portfolio.STM
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertFalse
import org.junit.jupiter.api.Assertions.assertSame
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

class NestedPortfolioNodeTest {

  private val config = XcfaConfig<SpecFrontendConfig, SpecBackendConfig>()
  private val safe = SafetyResult.safe<EmptyProof, EmptyCex>(EmptyProof.getInstance())

  private fun leaf(name: String, fail: Boolean = false) =
    ConfigNode(name, config) { if (fail) throw RuntimeException(name) else safe }

  @Test
  fun `nested portfolio reports the inner config that succeeded`() {
    val nested =
      NestedPortfolioNode("Nested") {
        val first = leaf("InnerFirst", fail = true)
        val second = leaf("InnerSecond")
        STM(first, setOf(Edge(first, second, { true })))
      }
    val result = STM(nested, emptySet()).execute(NullLogger.getInstance())

    assertEquals("InnerSecond", (result.first as Pair<*, *>).first)
    assertSame(safe, result.second)
  }

  @Test
  fun `failing nested portfolio falls back in the outer portfolio`() {
    val nested = NestedPortfolioNode("Nested") { STM(leaf("Inner", fail = true), emptySet()) }
    val fallback = leaf("Fallback")
    val result =
      STM(nested, setOf(Edge(nested, fallback, { true }))).execute(NullLogger.getInstance())

    assertEquals("Fallback", (result.first as Pair<*, *>).first)
  }

  @Test
  fun `nested portfolio is built only when needed`() {
    var built = false
    val nested =
      NestedPortfolioNode("Nested") {
        built = true
        STM(leaf("Inner"), emptySet())
      }
    val stm = STM(nested, setOf(Edge(nested, leaf("Other"), { true })))
    assertTrue(stm.visualize().contains("Nested: nested portfolio"))
    assertFalse(built)

    nested.innerSTM
    assertTrue(built)
  }
}
