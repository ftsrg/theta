/*
 *  Copyright 2023 Budapest University of Technology and Economics
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

import hu.bme.mit.theta.analysis.expr.refinement.PruneStrategy
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.xcfa.analysis.ErrorDetection
import hu.bme.mit.theta.xcfa.cli.*
import hu.bme.mit.theta.xcfa.cli.portfolio.*
import hu.bme.mit.theta.xcfa.model.XCFA

val xcfaTyped = xcfa as XCFA
val cFileNameTyped = cFileName as String
val loggerTyped = logger as Logger
val smtHomeTyped = smtHome as String
val traitsTyped = traits as VerificationTraits
val propertyTyped = property as ErrorDetection
val parseContextTyped = parseContext as ParseContext

val checker = { p: Boolean, config: XcfaCegarConfig ->
    if (p)
        config.checkInProcessDebug(xcfaTyped, smtHomeTyped, true, cFileNameTyped, loggerTyped, parseContextTyped)()
    else config.check(xcfaTyped, loggerTyped)
}

var baseConfig = XcfaCegarConfig(
    errorDetectionType = propertyTyped,
    abstractionSolver = "Z3",
    validateAbstractionSolver = false,
    domain = Domain.EXPL,
    maxEnum = 1,
    search = Search.ERR,
    initPrec = InitPrec.EMPTY,
    porLevel = POR.NOPOR,
    refinementSolver = "Z3",
    validateRefinementSolver = false,
    refinement = Refinement.SEQ_ITP,
    exprSplitter = ExprSplitterOptions.WHOLE,
    pruneStrategy = PruneStrategy.FULL,
    cexMonitor = CexMonitorOptions.DISABLE,
    timeoutMs = 0
)

if (traitsTyped.multithreaded) {
    baseConfig = baseConfig.copy(search = Search.BFS, porLevel = POR.AASPOR, pruneStrategy = PruneStrategy.LAZY)

    if (propertyTyped == ErrorDetection.DATA_RACE) {
        baseConfig = baseConfig.copy(porLevel = POR.SPOR)
    }
}

val timeoutOrSolverError = ExceptionTrigger(
    ErrorCodeException(ExitCodes.SOLVER_ERROR.code),
    ErrorCodeException(ExitCodes.TIMEOUT.code),
    ErrorCodeException(ExitCodes.VERIFICATION_STUCK.code),
    ErrorCodeException(ExitCodes.OUT_OF_MEMORY.code),
    ErrorCodeException(ExitCodes.GENERIC_ERROR.code),
    label = "TimeoutOrSolverError"
)

val quickExplConfig = baseConfig.copy(initPrec = InitPrec.ALLVARS, timeoutMs = 10_000)
val emptyExplConfig = baseConfig.copy(timeoutMs = 10_000)
val predConfig = baseConfig.copy(domain = Domain.PRED_CART, refinement = Refinement.BW_BIN_ITP, timeoutMs = 10_000)

val inProcess = true

val config_1_2 = ConfigNode("QuickFullExpl_Z3_$inProcess", quickExplConfig.copy(), checker, inProcess)
val config_2_2 = ConfigNode("EmptyExpl_Z3_$inProcess", emptyExplConfig.copy(), checker, inProcess)
val config_3_2 = ConfigNode("PredCart_Z3_$inProcess", predConfig.copy(), checker, inProcess)

val timeouts = setOf(
    Edge(config_1_2, config_2_2, timeoutOrSolverError),
    Edge(config_2_2, config_3_2, timeoutOrSolverError),
)
STM(config_1_2, timeouts).execute()
