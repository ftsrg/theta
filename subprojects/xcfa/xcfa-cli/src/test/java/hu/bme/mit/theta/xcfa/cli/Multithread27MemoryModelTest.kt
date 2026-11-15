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
import hu.bme.mit.theta.xcfa.cli.portfolio.ExceptionTrigger
import hu.bme.mit.theta.xcfa.cli.portfolio.Node
import hu.bme.mit.theta.xcfa.cli.portfolio.STM
import hu.bme.mit.theta.xcfa.cli.portfolio.multithreadPortfolio27
import hu.bme.mit.theta.xcfa.model.procedure
import hu.bme.mit.theta.xcfa.model.xcfa
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.EnumSource

/**
 * The OC nodes leave the memory model to the frontend and its fallbacks, or use the one an earlier
 * fallback pinned. A stronger model is only tried after a failure other than a timeout, except for
 * the `flat` retry after the first slice of an unpinned step, and no node runs right before a copy
 * of itself.
 */
class Multithread27MemoryModelTest {

  private fun program() =
    xcfa("") {
      val main =
        procedure("main") {
          "x" type Int()
          (init to final) { "x".assign("0") }
        }
      main.start()
    }

  private fun stm(property: ErrorDetection, pinned: MemoryModelType?, arrays: Boolean): STM {
    val xcfaProperty =
      XcfaProperty(property).also {
        if (property != ErrorDetection.DATA_RACE)
          it.transformSpecification(ErrorDetection.ERROR_LOCATION)
      }
    val parseContext = ParseContext().apply { if (arrays) addArithmeticTrait(ArithmeticTrait.ARR) }
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

  private fun ocNodes(stm: STM) =
    reachable(stm).filterIsInstance<ConfigNode>().filter { it.name.startsWith("MULTITHREAD_OC_") }

  private val ConfigNode.memoryModel
    get() = (config.frontendConfig.specConfig as CFrontendConfig).memoryModel

  @ParameterizedTest
  @EnumSource(names = ["ERROR_LOCATION", "DATA_RACE", "OVERFLOW", "MEMSAFETY"])
  fun aStrongerModelOnlyAfterAFailureOtherThanATimeout(property: ErrorDetection) {
    for (pinned in listOf(null, MemoryModelType.flat, MemoryModelType.bytes)) {
      for (arrays in listOf(false, true)) {
        val stm = stm(property, pinned, arrays)
        val start = stm.initNode as ConfigNode
        assertEquals(pinned, start.memoryModel, "$property, pinned $pinned: ${start.name}")
        val nodes = ocNodes(stm)
        nodes.forEach { node ->
          val model = node.memoryModel
          assertTrue(model == pinned || model!! > (pinned ?: MemoryModelType.multi), node.name)
        }
        reachable(stm).forEach { from ->
          from.outEdges
            .filter { it.target in nodes && (it.target as ConfigNode).memoryModel != pinned }
            .forEach { edge ->
              val slice =
                pinned == null &&
                  from in nodes &&
                  (from as ConfigNode).memoryModel == null &&
                  (edge.target as ConfigNode).memoryModel == MemoryModelType.flat
              if (slice) return@forEach
              val trigger = (edge.trigger as ExceptionTrigger).label
              assertEquals("AnythingButTimeout", trigger, "${from.name} -> ${edge.target.name}")
            }
        }
      }
    }
  }

  @ParameterizedTest
  @EnumSource(names = ["ERROR_LOCATION", "DATA_RACE", "OVERFLOW", "MEMSAFETY"])
  fun noNodeRunsBeforeItsCopy(property: ErrorDetection) {
    for (pinned in listOf(null, MemoryModelType.flat, MemoryModelType.bytes)) {
      for (arrays in listOf(false, true)) {
        reachable(stm(property, pinned, arrays)).forEach { node ->
          node.outEdges.forEach { edge ->
            val (from, to) = edge.source to edge.target
            if (from is ConfigNode && to is ConfigNode)
              assertTrue(from.run() != to.run(), "$property, pinned $pinned: ${from.name} twice")
          }
        }
      }
    }
  }
}
