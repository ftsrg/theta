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

    fun mddCegar(timeout: Long, solver: String, unroll: Int = -1) =
      ConfigNode(
        "MDD-cegar-${solver}${if (unroll > 0) "-unroll$unroll" else ""}-$inProcess",
        XcfaConfig(
          inputConfig = baseMddConfig.inputConfig,
          frontendConfig = baseMddConfig.frontendConfig.copy(forceUnroll = unroll),
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

    val memsafety =
      portfolioConfig.inputConfig.property.inputProperty in setOf(MEMSAFETY, MEMCLEANUP)
    val next = if (inProcess) anythingButServerError else anyError

    // A 2 x n matrix over the loop unroll bound: a stuck step (safe on cut loops) moves on to the
    // next bound, any other failure of MDD to MDD_CEGAR with the same bound.
    val bounds = listOf(-1, 5, 10)
    val mdds =
      bounds.map { mdd(if (memsafety) 0 else if (it < 0) 300_000 else 150_000, "Z3:new", it) }
    val cegars = bounds.map { mddCegar(0, "mathsat:latest", it) }
    mdds.zipWithNext { a, b -> edges.add(Edge(a, b, verificationStuck)) }
    if (memsafety) return STM(mdds.first(), edges)
    cegars.zipWithNext { a, b -> edges.add(Edge(a, b, verificationStuck)) }
    mdds.zip(cegars) { a, b -> edges.add(Edge(a, b, next)) }

    return STM(mdds.first(), edges)
  }

  logger.benchmark("Using portfolio: SYMBOLIC\n")

  val inProcess = HierarchicalNode("InProcess", getStm(true))
  val notInProcess = HierarchicalNode("NotInprocess", getStm(false))
  val fallbackEdge = Edge(inProcess, notInProcess, anyError)

  return if (portfolioConfig.debugConfig.debug) getStm(false)
  else STM(inProcess, setOf(fallbackEdge))
}
