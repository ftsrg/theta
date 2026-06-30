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
      maxOf(ocConfig.forceUnrollBoundStart, witnessMaxLocationRevisits(witnessFile)) to -1
    } ?: (ocConfig.forceUnrollBoundStart to ocConfig.forceUnrollBoundEnd)

  val ocChecker =
    XcfaOcChecker(
      xcfa = xcfa,
      property = config.inputConfig.property.verifiedProperty,
      parseContext = parseContext,
      decisionProcedure = ocConfig.decisionProcedure,
      smtSolver = ocConfig.smtSolver,
      logger = logger,
      conflictInput = ocConfig.inputConflictClauseFile,
      outputConflictClauses = ocConfig.outputConflictClauses,
      nonPermissiveValidation = ocConfig.nonPermissiveValidation,
      autoConflictConfig = ocConfig.autoConflict,
      autoConflictBound = ocConfig.autoConflictBound,
      memoryModel = ocConfig.memoryConsistencyModel,
      acceptUnreliableSafe = config.outputConfig.acceptUnreliableSafe,
      forceUnrollBoundStart = forceUnrollBoundStart,
      forceUnrollBoundEnd = forceUnrollBoundEnd,
      forceUnrollBoundStep = ocConfig.forceUnrollBoundStep,
    )
  return SafetyChecker { ocChecker.check() }
}

/**
 * The deepest loop trip count a violation witness requires to be followed: a waypoint sitting on a
 * loop body recurs once per witnessed iteration, so the maximum number of (non-`avoid`) waypoints
 * sharing a single source location is how many times that loop must be unrolled.
 */
private fun witnessMaxLocationRevisits(witnessFile: File): Int {
  val witness =
    WitnessYamlConfig.decodeFromString(
        ListSerializer(YamlWitness.serializer()),
        witnessFile.readText(),
      )[0]
  return witness.content
    .mapNotNull { it.segment }
    .flatten()
    .filter { it.waypoint.action != Action.AVOID }
    .groupingBy { it.waypoint.location }
    .eachCount()
    .values
    .maxOrNull() ?: 0
}
