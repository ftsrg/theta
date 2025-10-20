/*
 *  Copyright 2025 Budapest University of Technology and Economics
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
import hu.bme.mit.theta.graphsolver.patterns.constraints.MCM
import hu.bme.mit.theta.xcfa.analysis.XcfaPrec
import hu.bme.mit.theta.xcfa.analysis.oc.XcfaOcChecker
import hu.bme.mit.theta.xcfa.cli.params.OcConfig
import hu.bme.mit.theta.xcfa.cli.params.XcfaConfig
import hu.bme.mit.theta.xcfa.model.XCFA

fun getOcChecker(
  xcfa: XCFA,
  mcm: MCM,
  config: XcfaConfig<*, *>,
  logger: Logger,
): SafetyChecker<EmptyProof, Cex, XcfaPrec<*>> {
  val ocConfig = config.backendConfig.specConfig as OcConfig
  val ocChecker =
    XcfaOcChecker(
      xcfa = xcfa,
      property = config.inputConfig.property,
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
    )
  return SafetyChecker { ocChecker.check() }
}
