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
import hu.bme.mit.theta.xcfa.ErrorDetection.MEMCLEANUP
import hu.bme.mit.theta.xcfa.ErrorDetection.MEMSAFETY
import hu.bme.mit.theta.xcfa.cli.params.*
import hu.bme.mit.theta.xcfa.cli.runConfig
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.passes.structure.LbePass.LbeLevel.LBE_LOCAL

/** Time for each MDD step that retries with the loops unrolled further. */
private const val UNROLLED_TIMEOUT_MS = 150_000L

fun symbolicPortfolio(
  xcfa: XCFA,
  mcm: MCM,
  parseContext: ParseContext,
  portfolioConfig: XcfaConfig<*, *>,
  logger: Logger,
  uniqueLogger: Logger,
): STM {

  val checker = { config: XcfaConfig<*, *> -> runConfig(config, logger, uniqueLogger, true) }

  val baseMddConfig =
    (baseMddConfig(portfolioConfig) as XcfaConfig<SpecFrontendConfig, MddConfig>).let {
      it.copy(frontendConfig = it.frontendConfig.copy(lbeLevel = LBE_LOCAL))
    }

  fun getStm(inProcess: Boolean): STM {
    val edges = LinkedHashSet<Edge>()

    fun mdd(timeout: Long, solver: String, unroll: Int = -1) =
      ConfigNode(
        "MDD-${solver}${if (unroll > 0) "-unroll$unroll" else ""}-$inProcess",
        baseMddConfig.copy(
          frontendConfig = baseMddConfig.frontendConfig.copy(forceUnroll = unroll),
          backendConfig =
            baseMddConfig.backendConfig.copy(
              timeoutMs = timeout,
              inProcess = inProcess,
              specConfig =
                baseMddConfig.backendConfig.specConfig!!.copy(
                  solver = solver,
                  iterationStrategy = GSAT,
                  symbolicValues = true,
                ),
            ),
        ),
        checker,
      )

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
              specConfig = MddCegarConfig(solver = solver, iterationStrategy = GSAT),
            ),
          outputConfig = baseMddConfig.outputConfig,
          debugConfig = baseMddConfig.debugConfig,
        ),
        checker,
      )
    }

    val next = if (inProcess) anythingButServerError else anyError

    // A safe verdict on cut loops is not trusted (the MDD gets stuck), but a violation within more
    // iterations is real. Added before the other edges of `from`, so a stuck MDD takes it first.
    fun unrolledAfterStuck(from: Node): Node {
      val steps = (3..5).map { mdd(UNROLLED_TIMEOUT_MS, "Z3:new", it) }
      edges.add(Edge(from, steps.first(), verificationStuck))
      steps.zipWithNext { a, b -> edges.add(Edge(a, b, next)) }
      return steps.last()
    }

    if (portfolioConfig.inputConfig.property.inputProperty in setOf(MEMSAFETY, MEMCLEANUP)) {
      val start = mdd(0, "Z3:new")
      unrolledAfterStuck(start)
      return STM(start, edges)
    }
    val start = mdd(300_000, "Z3:new")
    val unrolled = unrolledAfterStuck(start)
    val (cegar, cegarTwin) = step(mddCegar, 0, "mathsat:latest", "Z3")
    edges.addAll(chainEdges(listOf(start to start), cegar, inProcess))
    edges.add(Edge(unrolled, cegar, next))
    edges.add(Edge(cegar, cegarTwin, solverError))

    return STM(start, edges)
  }

  logger.benchmark("Using portfolio: SYMBOLIC\n")

  val inProcess = HierarchicalNode("InProcess", getStm(true))
  val notInProcess = HierarchicalNode("NotInprocess", getStm(false))
  val fallbackEdge = Edge(inProcess, notInProcess, anyError)

  return if (portfolioConfig.debugConfig.debug) getStm(false)
  else STM(inProcess, setOf(fallbackEdge))
}
