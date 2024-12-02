/*
 *  Copyright 2024 Budapest University of Technology and Economics
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

import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.Checker
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.algorithm.arg.ARG
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.graphsolver.patterns.constraints.MCM
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaPrec
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.cli.params.Backend
import hu.bme.mit.theta.xcfa.cli.params.XcfaConfig
import hu.bme.mit.theta.xcfa.model.XCFA

fun getSafetyChecker(
  xcfa: XCFA,
  mcm: MCM,
  config: XcfaConfig<*, *>,
  parseContext: ParseContext,
  logger: Logger,
  uniqueLogger: Logger,
): SafetyChecker<*, *, *> =
  if (config.backendConfig.inProcess) {
    InProcessChecker(xcfa, config, parseContext, logger)
  } else {
    when (config.backendConfig.backend) {
      Backend.CEGAR -> getCegarChecker(xcfa, mcm, config, logger)
      Backend.BOUNDED -> getBoundedChecker(xcfa, mcm, parseContext, config, logger)
      Backend.OC -> getOcChecker(xcfa, mcm, config, logger)
      Backend.LAZY -> TODO()
      Backend.PORTFOLIO ->
        getPortfolioChecker(xcfa, mcm, config, parseContext, logger, uniqueLogger)
      Backend.MDD -> getMddChecker(xcfa, mcm, parseContext, config, logger)
      Backend.NONE ->
        SafetyChecker<
          ARG<XcfaState<PtrState<*>>, XcfaAction>,
          Trace<XcfaState<PtrState<*>>, XcfaAction>,
          XcfaPrec<*>,
        > { _ ->
          SafetyResult.unknown()
        }
      Backend.CHC -> getHornChecker(xcfa, mcm, config, logger)
      Backend.TRACEGEN ->
        throw RuntimeException(
          "Trace generation is NOT safety analysis, can not return safety checker for trace generation"
        )
    }
  }

fun getChecker(
  xcfa: XCFA,
  mcm: MCM,
  config: XcfaConfig<*, *>,
  parseContext: ParseContext,
  logger: Logger,
  uniqueLogger: Logger,
): Checker<*, XcfaPrec<*>> =
  if (config.backendConfig.inProcess) {
    InProcessChecker(xcfa, config, parseContext, logger)
  } else {
    when (config.backendConfig.backend) {
      Backend.TRACEGEN -> getTracegenChecker(xcfa, mcm, config, logger)
      Backend.CEGAR ->
        throw RuntimeException(
          "Use getSafetyChecker method for safety analysis instead of getChecker"
        )
      Backend.BOUNDED ->
        throw RuntimeException(
          "Use getSafetyChecker method for safety analysis instead of getChecker"
        )
      Backend.OC ->
        throw RuntimeException(
          "Use getSafetyChecker method for safety analysis instead of getChecker"
        )
      Backend.LAZY ->
        throw RuntimeException(
          "Use getSafetyChecker method for portfolio safety analysis instead of getChecker"
        )
      Backend.PORTFOLIO ->
        throw RuntimeException(
          "Use getSafetyChecker method for portfolio safety analysis instead of getChecker"
        )
      Backend.NONE ->
        SafetyChecker<
          ARG<XcfaState<PtrState<*>>, XcfaAction>,
          Trace<XcfaState<PtrState<*>>, XcfaAction>,
          XcfaPrec<*>,
        > { _ ->
          SafetyResult.unknown()
        }
      Backend.CHC ->
        throw RuntimeException(
          "Use getSafetyChecker method for safety analysis instead of getChecker"
        )

      Backend.MDD ->
        throw RuntimeException(
          "Use getSafetyChecker method for portfolio safety analysis instead of getChecker"
        )
    }
  }
