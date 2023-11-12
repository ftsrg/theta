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
    noCexCheck = false,
    timeoutMs = 120_000
)

if (traitsTyped.multithreaded) {
    baseConfig = baseConfig.copy(search = Search.BFS, porLevel = POR.AAPOR,
        pruneStrategy = PruneStrategy.LAZY)

    if (propertyTyped == ErrorDetection.DATA_RACE) {
        baseConfig = baseConfig.copy(porLevel = POR.BASIC)
    }
}

baseConfig.checkInProcess(xcfaTyped, smtHomeTyped, true, cFileNameTyped, loggerTyped)()

