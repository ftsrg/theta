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
package hu.bme.mit.theta.xcfa.cli.portfolio

import hu.bme.mit.theta.analysis.algorithm.mdd.fixedpoint.IterationStrategy.GSAT
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.graphsolver.patterns.constraints.MCM
import hu.bme.mit.theta.xcfa.cli.params.*
import hu.bme.mit.theta.xcfa.cli.runConfig
import hu.bme.mit.theta.xcfa.model.XCFA

fun symbolicPortfolio(
  xcfa: XCFA,
  mcm: MCM,
  parseContext: ParseContext,
  portfolioConfig: XcfaConfig<*, *>,
  logger: Logger,
  uniqueLogger: Logger,
): STM {

  val checker = { config: XcfaConfig<*, *> -> runConfig(config, logger, uniqueLogger, true) }

  val baseMddConfig = baseMddConfig(xcfa, mcm, parseContext, portfolioConfig, false)

  fun getStm(inProcess: Boolean): STM {
    val edges = LinkedHashSet<Edge>()

    val mdd = { timeout: Long, solver: String ->
      ConfigNode(
        "MDD-${solver}-$inProcess",
        baseMddConfig.copy(
          backendConfig =
            baseMddConfig.backendConfig.copy(
              timeoutMs = timeout,
              inProcess = inProcess,
              parseInProcess = true,
              specConfig =
                baseMddConfig.backendConfig.specConfig!!.copy(
                  solver = solver,
                  iterationStrategy = GSAT,
                ),
            )
        ),
        checker,
      )
    }

    val mddCegar = { timeout: Long, solver: String ->
      ConfigNode(
        "MDD-cegar-${solver}-$inProcess",
        XcfaConfig(
          inputConfig = baseMddConfig.inputConfig,
          frontendConfig = baseMddConfig.frontendConfig,
          backendConfig =
            BackendConfig(
              backend = Backend.MDD_CEGAR,
              memlimit = baseMddConfig.backendConfig.memlimit,
              solverHome = baseMddConfig.backendConfig.solverHome,
              timeoutMs = timeout,
              inProcess = inProcess,
              parseInProcess = true,
              specConfig = MddCegarConfig(solver = solver, iterationStrategy = GSAT),
            ),
          outputConfig = baseMddConfig.outputConfig,
          debugConfig = baseMddConfig.debugConfig,
        ),
        checker,
      )
    }

    infix fun Node.then(node: Node): Node {
      edges.add(Edge(this, node, if (inProcess) timeoutOrNotSolvableError else anyError))
      return node
    }

    val start = mdd(300_000, "Z3")
    start then mddCegar(0, "mathsat:5.6.10")

    return STM(start, edges)
  }

  logger.benchmark("Using portfolio: SYMBOLIC\n")

  val inProcess = HierarchicalNode("InProcess", getStm(true))
  val notInProcess = HierarchicalNode("NotInprocess", getStm(false))
  val fallbackEdge = Edge(inProcess, notInProcess, anyError)

  return if (portfolioConfig.debugConfig.debug) getStm(false)
  else STM(inProcess, setOf(fallbackEdge))
}
