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
package hu.bme.mit.theta.xcfa.cli.checkers

import hu.bme.mit.theta.analysis.Cex
import hu.bme.mit.theta.analysis.algorithm.EmptyProof
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.solver.SolverManager
import hu.bme.mit.theta.solver.validator.SolverValidatorWrapperFactory
import hu.bme.mit.theta.xcfa.analysis.XcfaPrec
import hu.bme.mit.theta.xcfa.analysis.oc.XcfaOcChecker
import hu.bme.mit.theta.xcfa.cli.params.OcConfig
import hu.bme.mit.theta.xcfa.cli.params.XcfaConfig
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.witnesses.Action
import hu.bme.mit.theta.xcfa.witnesses.WitnessYamlConfig
import hu.bme.mit.theta.xcfa.witnesses.YamlWitness
import java.io.File
import kotlinx.serialization.builtins.ListSerializer

fun getOcChecker(
  xcfa: XCFA,
  parseContext: ParseContext,
  config: XcfaConfig<*, *>,
  logger: Logger,
): SafetyChecker<EmptyProof, Cex, XcfaPrec<*>> {
  val ocConfig = config.backendConfig.specConfig as OcConfig

  val (forceUnrollBoundStart, forceUnrollBoundEnd) =
    config.inputConfig.witness?.let { witnessFile ->
      maxOf(ocConfig.forceUnrollBoundStart, witnessUnrollBound(witnessFile)) to -1
    } ?: (ocConfig.forceUnrollBoundStart to ocConfig.forceUnrollBoundEnd)

  val ocChecker =
    XcfaOcChecker(
      xcfa = xcfa,
      property = config.inputConfig.property,
      parseContext = parseContext,
      decisionProcedure = ocConfig.decisionProcedure,
      solverFactory = ocSolverFactory(ocConfig),
      logger = logger,
      outputConflictClauses = ocConfig.outputConflictClauses,
      autoConflictConfig = ocConfig.autoConflict,
      autoConflictBound = ocConfig.autoConflictBound,
      memoryModel = ocConfig.memoryConsistencyModel,
      acceptUnreliableSafe = config.outputConfig.acceptUnreliableSafe,
      forceUnrollBoundStart = forceUnrollBoundStart,
      forceUnrollBoundEnd = forceUnrollBoundEnd,
      forceUnrollBoundStep = ocConfig.forceUnrollBoundStep,
      maxExitQueries = ocConfig.maxExitQueries,
    )
  return SafetyChecker { ocChecker.check() }
}

private fun ocSolverFactory(ocConfig: OcConfig): SolverFactory {
  val solverFactory = SolverManager.resolveSolverFactory(ocConfig.smtSolver)
  if (!ocConfig.validateSolver && ocConfig.unsatReferenceSolver.isEmpty()) return solverFactory
  val unsatReference =
    ocConfig.unsatReferenceSolver
      .takeIf { it.isNotEmpty() }
      ?.let { SolverManager.resolveSolverFactory(it) }
  return SolverValidatorWrapperFactory.create(solverFactory, unsatReference)
}

/**
 * The loop trip count to start validating a witness with: a waypoint recurs once per witnessed
 * iteration, and each thread unrolls its own copy, so this is the maximum number of (non-`avoid`)
 * waypoints of one thread at one source location, minus one as a loop head is also passed on exit.
 * A too small bound is only a start: the cut loop's exit stays reachable, so OC deepens it.
 */
private fun witnessUnrollBound(witnessFile: File): Int =
  witnessUnrollBound(
    WitnessYamlConfig.decodeFromString(
        ListSerializer(YamlWitness.serializer()),
        witnessFile.readText(),
      )[0]
  )

internal fun witnessUnrollBound(witness: YamlWitness): Int =
  witness.content
    .mapNotNull { it.segment }
    .flatten()
    .filter { it.waypoint.action != Action.AVOID }
    .groupingBy { it.waypoint.location to it.waypoint.threadId }
    .eachCount()
    .values
    .maxOrNull()
    ?.minus(1) ?: 0
