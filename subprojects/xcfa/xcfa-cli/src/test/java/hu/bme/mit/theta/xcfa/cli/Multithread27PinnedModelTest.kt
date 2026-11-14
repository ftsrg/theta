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

import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.MemoryModelType
import hu.bme.mit.theta.frontend.transformation.grammar.preprocess.ArithmeticTrait
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.cli.params.*
import hu.bme.mit.theta.xcfa.cli.portfolio.ConfigNode
import hu.bme.mit.theta.xcfa.cli.portfolio.Node
import hu.bme.mit.theta.xcfa.cli.portfolio.STM
import hu.bme.mit.theta.xcfa.cli.portfolio.multithreadPortfolio27
import hu.bme.mit.theta.xcfa.model.procedure
import hu.bme.mit.theta.xcfa.model.xcfa
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.EnumSource

/**
 * A memory model pinned by a frontend fallback raises the OC nodes of weaker models to it, which
 * makes some of them copies of the node after them: none may run right before its copy.
 */
class Multithread27PinnedModelTest {

  private fun program() =
    xcfa("") {
      val main =
        procedure("main") {
          "x" type Int()
          (init to final) { "x".assign("0") }
        }
      main.start()
    }

  private fun stm(property: ErrorDetection, pinned: MemoryModelType?): STM {
    val xcfaProperty =
      XcfaProperty(property).also {
        if (property != ErrorDetection.DATA_RACE)
          it.transformSpecification(ErrorDetection.ERROR_LOCATION)
      }
    val parseContext = ParseContext().apply { addArithmeticTrait(ArithmeticTrait.ARR) }
    return multithreadPortfolio27(
      program(),
      emptySet(),
      parseContext,
      XcfaConfig<SpecFrontendConfig, SpecBackendConfig>(
        inputConfig = InputConfig(property = xcfaProperty),
        frontendConfig =
          FrontendConfig<SpecFrontendConfig>(specConfig = CFrontendConfig(memoryModel = pinned)),
        debugConfig = DebugConfig(debug = true),
      ),
      NullLogger.getInstance(),
      NullLogger.getInstance(),
    )
  }

  private fun reachable(stm: STM): Set<Node> {
    val all = mutableSetOf<Node>()
    val queue = ArrayDeque(listOf(stm.initNode))
    while (queue.isNotEmpty()) {
      val node = queue.removeFirst()
      if (all.add(node)) node.outEdges.forEach { queue.addLast(it.target) }
    }
    return all
  }

  private fun ConfigNode.run() = name to config.frontendConfig.ptrSizeInMemory

  @ParameterizedTest
  @EnumSource(names = ["ERROR_LOCATION", "DATA_RACE", "OVERFLOW", "MEMSAFETY"])
  fun noNodeRunsBeforeItsCopy(property: ErrorDetection) {
    for (pinned in listOf(null, MemoryModelType.flat, MemoryModelType.bytes)) {
      reachable(stm(property, pinned)).forEach { node ->
        node.outEdges.forEach { edge ->
          val (from, to) = edge.source to edge.target
          if (from is ConfigNode && to is ConfigNode)
            assertTrue(from.run() != to.run(), "$property, pinned $pinned: ${from.name} twice")
        }
      }
    }
  }

  @ParameterizedTest
  @EnumSource(names = ["ERROR_LOCATION", "DATA_RACE", "MEMSAFETY"])
  fun aPinnedFlatModelStartsWithTheFlatSlice(property: ErrorDetection) {
    val unpinned = stm(property, null).initNode.name
    assertTrue("_multi_" in unpinned, "unpinned start: $unpinned")
    val start = stm(property, MemoryModelType.flat).initNode as ConfigNode
    assertTrue("_flat_yices2" in start.name, "pinned start: ${start.name}")
    // the slice of the flat node, not of the multi node it replaces
    assertTrue(start.config.backendConfig.timeoutMs >= 500_000, "slice of ${start.name}")
  }

  @Test
  fun aSkippedCopyKeepsTheOrderOfTheEdges() {
    // under flat, the multi Z3 memsafety node is the flat Z3 one: after a failure other than a
    // timeout it goes on to the bytes model, after a timeout to CEGAR
    val nodes = reachable(stm(ErrorDetection.MEMSAFETY, MemoryModelType.flat))
    val z3 = nodes.filterIsInstance<ConfigNode>().single { "_flat_new" in it.name }
    val targets = z3.outEdges.map { it.target.name }
    assertEquals(2, targets.size, "$targets")
    assertTrue("_bytes_" in targets[0], "$targets")
    assertTrue(targets[1].startsWith("MULTITHREAD_EXPL_COI"), "$targets")
  }
}
