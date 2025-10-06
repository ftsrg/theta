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

import hu.bme.mit.theta.analysis.expr.refinement.PruneStrategy
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.frontend.transformation.grammar.preprocess.BitwiseOption
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.xcfa.analysis.ErrorDetection
import hu.bme.mit.theta.xcfa.cli.*
import hu.bme.mit.theta.xcfa.cli.portfolio.*
import hu.bme.mit.theta.xcfa.model.XCFA
import java.io.File
import java.util.concurrent.TimeoutException

val xcfaTyped = xcfa as XCFA
val cFileNameTyped = cFileName as String
val loggerTyped = logger as Logger
val smtHomeTyped = smtHome as String
val traitsTyped = traits as VerificationTraits
val propertyTyped = property as ErrorDetection
val parseContextTyped = parseContext as ParseContext

val checker = { p: Boolean, config: XcfaCegarConfig ->
    if (p)
        config.checkInProcess(xcfaTyped, smtHomeTyped, true, cFileNameTyped, loggerTyped, parseContextTyped)()
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
    por = POR.NOPOR,
    refinementSolver = "Z3",
    validateRefinementSolver = false,
    refinement = Refinement.SEQ_ITP,
    exprSplitter = ExprSplitterOptions.WHOLE,
    pruneStrategy = PruneStrategy.FULL,
    cexMonitor = CexMonitorOptions.CHECK,
    timeoutMs = 0
)

if (traitsTyped.multithreaded) {
    baseConfig = baseConfig.copy(search = Search.BFS, por = POR.AASPOR, pruneStrategy = PruneStrategy.LAZY)

    if (propertyTyped == ErrorDetection.DATA_RACE) {
        baseConfig = baseConfig.copy(por = POR.SPOR)
    }
}

val timeoutTrigger = ExceptionTrigger(
    ErrorCodeException(ExitCodes.TIMEOUT.code),
    ErrorCodeException(ExitCodes.VERIFICATION_STUCK.code),
    ErrorCodeException(ExitCodes.OUT_OF_MEMORY.code),
    ErrorCodeException(ExitCodes.GENERIC_ERROR.code),
    label = "Timeout"
)

val timeoutOrSolverError = ExceptionTrigger(
    ErrorCodeException(ExitCodes.SOLVER_ERROR.code),
    ErrorCodeException(ExitCodes.TIMEOUT.code),
    ErrorCodeException(ExitCodes.VERIFICATION_STUCK.code),
    ErrorCodeException(ExitCodes.OUT_OF_MEMORY.code),
    ErrorCodeException(ExitCodes.GENERIC_ERROR.code),
    label = "TimeoutOrSolverError"
)

val quickExplConfig = baseConfig.copy(initPrec = InitPrec.ALLVARS, timeoutMs = 90_000)
val emptyExplConfig = baseConfig.copy(timeoutMs = 210_000)
val predConfig = baseConfig.copy(domain = Domain.PRED_CART, refinement = Refinement.BW_BIN_ITP)

fun integerStm(): STM {
    fun getStm(inProcess: Boolean): STM {
        val config_1_1 = ConfigNode("QuickFullExpl_z3_4.10.1_$inProcess",
            quickExplConfig.copy(abstractionSolver = "z3:4.10.1", refinementSolver = "z3:4.10.1",
                refinement = Refinement.NWT_IT_WP), checker, inProcess)
        val config_2_1 = ConfigNode("EmptyExpl_z3_4.10.1_$inProcess",
            emptyExplConfig.copy(abstractionSolver = "z3:4.10.1", refinementSolver = "z3:4.10.1",
                refinement = Refinement.NWT_IT_WP), checker, inProcess)
        val config_3_1 = ConfigNode("PredCart_z3_4.10.1_$inProcess",
            predConfig.copy(abstractionSolver = "z3:4.10.1", refinementSolver = "z3:4.10.1"), checker, inProcess)

        val config_1_2 = ConfigNode("QuickFullExpl_Z3_$inProcess", quickExplConfig.copy(), checker, inProcess)
        val config_2_2 = ConfigNode("EmptyExpl_Z3_$inProcess", emptyExplConfig.copy(), checker, inProcess)
        val config_3_2 = ConfigNode("PredCart_Z3_$inProcess", predConfig.copy(), checker, inProcess)

        val config_1_3 = ConfigNode("QuickFullExpl_princess_2022_07_01_$inProcess",
            quickExplConfig.copy(abstractionSolver = "princess:2022-07-01", refinementSolver = "princess:2022-07-01"),
            checker, inProcess)
        val config_2_3 = ConfigNode("EmptyExpl_princess_2022_07_01_$inProcess",
            emptyExplConfig.copy(abstractionSolver = "princess:2022-07-01", refinementSolver = "princess:2022-07-01"),
            checker, inProcess)
        val config_3_3 = ConfigNode("PredCart_mathsat_5.6.8_$inProcess",
            predConfig.copy(abstractionSolver = "mathsat:5.6.8", refinementSolver = "mathsat:5.6.8"), checker,
            inProcess)

        val config_1_4 = ConfigNode("QuickFullExpl_mathsat_5.6.8_$inProcess",
            quickExplConfig.copy(abstractionSolver = "mathsat:5.6.8", refinementSolver = "mathsat:5.6.8"), checker,
            inProcess)
        val config_2_4 = ConfigNode("EmptyExpl_mathsat_5.6.8_$inProcess",
            emptyExplConfig.copy(abstractionSolver = "mathsat:5.6.8", refinementSolver = "mathsat:5.6.8"), checker,
            inProcess)
        val config_3_4 = ConfigNode("PredCart_princess_2022_07_01_$inProcess",
            predConfig.copy(abstractionSolver = "princess:2022-07-01", refinementSolver = "princess:2022-07-01"),
            checker, inProcess)

        val timeouts = setOf(
            Edge(config_1_1, config_2_1, timeoutTrigger),
            Edge(config_2_1, config_3_1, timeoutTrigger),

            Edge(config_1_2, config_2_2, timeoutTrigger),
            Edge(config_2_2, config_3_1, timeoutTrigger),

            Edge(config_1_3, config_2_3, timeoutTrigger),
            Edge(config_2_3, config_3_1, timeoutTrigger),

            Edge(config_1_4, config_2_4, if (inProcess) timeoutOrSolverError else ExceptionTrigger(label = "Anything")),
            Edge(config_2_4, config_3_1, if (inProcess) timeoutOrSolverError else ExceptionTrigger(label = "Anything")),
        )

        val notTimeout = if (inProcess) ExceptionTrigger(ErrorCodeException(ExitCodes.SOLVER_ERROR.code),
            label = "SolverError") else ExceptionTrigger(fallthroughExceptions = timeoutTrigger.exceptions,
            label = "AnythingButTimeout")

        val solverExceptions = setOf(
            Edge(config_1_1, config_1_2, notTimeout),
            Edge(config_1_2, config_1_3, notTimeout),
            Edge(config_1_3, config_1_4, notTimeout),

            Edge(config_2_1, config_2_2, notTimeout),
            Edge(config_2_2, config_2_3, notTimeout),
            Edge(config_2_3, config_2_4, notTimeout),

            Edge(config_3_1, config_3_2, notTimeout),
            Edge(config_3_2, config_3_3, notTimeout),
            Edge(config_3_3, config_3_4, notTimeout),
        )
        return STM(config_1_1, timeouts union solverExceptions)
    }

    val inProcess = HierarchicalNode("InProcess", getStm(true))
    val notInProcess = HierarchicalNode("NotInprocess", getStm(false))

    val fallbackEdge = Edge(inProcess, notInProcess, ExceptionTrigger(label = "Anything"))

    return STM(inProcess, setOf(fallbackEdge))
}

fun bitwiseStm(): STM {
    fun getStm(inProcess: Boolean): STM {
        val config_1_1 = ConfigNode("QuickFullExpl_Z3_$inProcess",
            quickExplConfig.copy(refinement = Refinement.NWT_IT_WP), checker, inProcess)
        val config_2_1 = ConfigNode("EmptyExpl_Z3_$inProcess", emptyExplConfig.copy(refinement = Refinement.NWT_IT_WP),
            checker, inProcess)
        val config_3_1 = ConfigNode("PredCart_mathsat_5.6.8_$inProcess",
            predConfig.copy(abstractionSolver = "mathsat:5.6.8", refinementSolver = "mathsat:5.6.8"), checker,
            inProcess)

        val config_1_2 = ConfigNode("QuickFullExpl_cvc5_1.0.2_$inProcess",
            quickExplConfig.copy(abstractionSolver = "cvc5:1.0.2", refinementSolver = "cvc5:1.0.2",
                refinement = Refinement.NWT_IT_WP), checker, inProcess)
        val config_2_2 = ConfigNode("EmptyExpl_cvc5_1.0.2_$inProcess",
            emptyExplConfig.copy(abstractionSolver = "cvc5:1.0.2", refinementSolver = "cvc5:1.0.2",
                refinement = Refinement.NWT_IT_WP), checker, inProcess)
        val config_3_2 = ConfigNode("PredCart_z3_4.10.1_$inProcess",
            predConfig.copy(abstractionSolver = "z3:4.10.1", refinementSolver = "z3:4.10.1"), checker, inProcess)

        val config_1_3 = ConfigNode("QuickFullExpl_mathsat_5.6.8_$inProcess",
            quickExplConfig.copy(abstractionSolver = "mathsat:5.6.8", refinementSolver = "mathsat:5.6.8",
                refinement = Refinement.NWT_IT_WP), checker, inProcess)
        val config_2_3 = ConfigNode("EmptyExpl_mathsat_5.6.8_$inProcess",
            emptyExplConfig.copy(abstractionSolver = "mathsat:5.6.8", refinementSolver = "mathsat:5.6.8",
                refinement = Refinement.SEQ_ITP), checker, inProcess)
        val config_3_3 = ConfigNode("PredCart_cvc5_1.0.2_$inProcess",
            predConfig.copy(abstractionSolver = "cvc5:1.0.2", refinementSolver = "cvc5:1.0.2",
                refinement = Refinement.NWT_IT_WP), checker, inProcess)

        val timeouts = setOf(
            Edge(config_1_1, config_2_1, timeoutTrigger),
            Edge(config_2_1, config_3_1, timeoutTrigger),

            Edge(config_1_2, config_2_2, timeoutTrigger),
            Edge(config_2_2, config_3_1, timeoutTrigger),

            Edge(config_1_3, config_2_3, if (inProcess) timeoutOrSolverError else ExceptionTrigger(label = "Anything")),
            Edge(config_2_3, config_3_1, if (inProcess) timeoutOrSolverError else ExceptionTrigger(label = "Anything")),
        )

        val notTimeout = if (inProcess) ExceptionTrigger(ErrorCodeException(ExitCodes.SOLVER_ERROR.code),
            label = "SolverError") else ExceptionTrigger(fallthroughExceptions = timeoutTrigger.exceptions,
            label = "AnythingButTimeout")

        val solverExceptions = setOf(
            Edge(config_1_1, config_1_2, notTimeout),
            Edge(config_1_2, config_1_3, notTimeout),

            Edge(config_2_1, config_2_2, notTimeout),
            Edge(config_2_2, config_2_3, notTimeout),

            Edge(config_3_1, config_3_2, notTimeout),
            Edge(config_3_2, config_3_3, notTimeout),
        )
        return STM(config_1_1, timeouts union solverExceptions)
    }

    val inProcess = HierarchicalNode("InProcess", getStm(true))
    val notInProcess = HierarchicalNode("NotInprocess", getStm(false))

    val fallbackEdge = Edge(inProcess, notInProcess, ExceptionTrigger(label = "Anything"))

    return STM(inProcess, setOf(fallbackEdge))
}

fun floatsStm(): STM {
    fun getStm(inProcess: Boolean): STM {
        val config_1_1 = ConfigNode("QuickFullExpl_cvc5_1.0.2_$inProcess",
            quickExplConfig.copy(abstractionSolver = "cvc5:1.0.2", refinementSolver = "cvc5:1.0.2",
                refinement = Refinement.NWT_IT_WP), checker, inProcess)
        val config_2_1 = ConfigNode("EmptyExpl_cvc5_1.0.2_$inProcess",
            quickExplConfig.copy(abstractionSolver = "cvc5:1.0.2", refinementSolver = "cvc5:1.0.2",
                refinement = Refinement.NWT_IT_WP), checker, inProcess)
        val config_3_1 = ConfigNode("PredCart_mathsat_5.6.8_$inProcess",
            predConfig.copy(abstractionSolver = "mathsat:5.6.8", refinementSolver = "mathsat:5.6.8"), checker,
            inProcess)

        val config_1_2 = ConfigNode("QuickFullExpl_cvc5_1.0.2_seq_$inProcess",
            quickExplConfig.copy(abstractionSolver = "cvc5:1.0.2", refinementSolver = "cvc5:1.0.2",
                refinement = Refinement.SEQ_ITP), checker, inProcess)
        val config_2_2 = ConfigNode("EmptyExpl_cvc5_1.0.2_seq_$inProcess",
            emptyExplConfig.copy(abstractionSolver = "cvc5:1.0.2", refinementSolver = "cvc5:1.0.2",
                refinement = Refinement.SEQ_ITP), checker, inProcess)
        val config_3_2 = ConfigNode("PredCart_bitwuzla_latest_$inProcess",
            predConfig.copy(abstractionSolver = "bitwuzla:latest", refinementSolver = "bitwuzla:latest",
                refinement = Refinement.NWT_IT_WP), checker, inProcess)

        val config_1_3 = ConfigNode("QuickFullExpl_mathsat_5.6.8_$inProcess",
            quickExplConfig.copy(abstractionSolver = "mathsat:5.6.8", refinementSolver = "mathsat:5.6.8",
                validateAbstractionSolver = true, validateRefinementSolver = true, refinement = Refinement.NWT_IT_WP),
            checker, inProcess)
        val config_2_3 = ConfigNode("EmptyExpl_mathsat_5.6.8_$inProcess",
            emptyExplConfig.copy(abstractionSolver = "mathsat:5.6.8", refinementSolver = "mathsat:5.6.8",
                validateAbstractionSolver = true, validateRefinementSolver = true, refinement = Refinement.NWT_IT_WP),
            checker, inProcess)
        val config_3_3 = ConfigNode("PredCart_cvc5_1.0.2_$inProcess",
            predConfig.copy(abstractionSolver = "cvc5:1.0.2", refinementSolver = "cvc5:1.0.2",
                refinement = Refinement.NWT_IT_WP), checker, inProcess)

        val config_1_4 = ConfigNode("QuickFullExpl_mathsat_fp_$inProcess",
            quickExplConfig.copy(abstractionSolver = "mathsat:fp", refinementSolver = "mathsat:fp",
                validateAbstractionSolver = true, validateRefinementSolver = true), checker, inProcess)
        val config_2_4 = ConfigNode("EmptyExpl_mathsat_fp_$inProcess",
            emptyExplConfig.copy(abstractionSolver = "mathsat:fp", refinementSolver = "mathsat:fp",
                validateAbstractionSolver = true, validateRefinementSolver = true), checker, inProcess)
        val config_3_4 = ConfigNode("PredCart_mathsat_fp_$inProcess",
            predConfig.copy(abstractionSolver = "mathsat:fp", refinementSolver = "mathsat:fp",
                validateAbstractionSolver = true, validateRefinementSolver = true), checker, inProcess)

        val config_1_5 = ConfigNode("QuickFullExpl_Z3_$inProcess",
            quickExplConfig.copy(abstractionSolver = "Z3", refinementSolver = "Z3", validateAbstractionSolver = true,
                validateRefinementSolver = true, refinement = Refinement.NWT_IT_WP), checker, inProcess)
        val config_2_5 = ConfigNode("EmptyExpl_Z3_$inProcess",
            emptyExplConfig.copy(abstractionSolver = "Z3", refinementSolver = "Z3", validateAbstractionSolver = true,
                validateRefinementSolver = true, refinement = Refinement.NWT_IT_WP), checker, inProcess)
        val config_3_5 = ConfigNode("PredCart_Z3_$inProcess",
            predConfig.copy(abstractionSolver = "Z3", refinementSolver = "Z3", refinement = Refinement.NWT_IT_WP),
            checker, inProcess)

        val timeouts = setOf(
            Edge(config_1_1, config_2_1, timeoutTrigger),
            Edge(config_2_1, config_3_1, timeoutTrigger),

            Edge(config_1_2, config_2_2, timeoutTrigger),
            Edge(config_2_2, config_3_1, timeoutTrigger),

            Edge(config_1_3, config_2_3, timeoutTrigger),
            Edge(config_2_3, config_3_1, timeoutTrigger),

            Edge(config_1_4, config_2_4, timeoutTrigger),
            Edge(config_2_4, config_3_1, timeoutTrigger),

            Edge(config_1_5, config_2_5, if (inProcess) timeoutOrSolverError else ExceptionTrigger(label = "Anything")),
            Edge(config_2_5, config_3_1, if (inProcess) timeoutOrSolverError else ExceptionTrigger(label = "Anything")),
        )

        val notTimeout = if (inProcess) ExceptionTrigger(ErrorCodeException(ExitCodes.SOLVER_ERROR.code),
            label = "SolverError") else ExceptionTrigger(fallthroughExceptions = timeoutTrigger.exceptions,
            label = "AnythingButTimeout")

        val solverExceptions = setOf(
            Edge(config_1_1, config_1_2, notTimeout),
            Edge(config_1_2, config_1_3, notTimeout),
            Edge(config_1_3, config_1_4, notTimeout),
            Edge(config_1_4, config_1_5, notTimeout),

            Edge(config_2_1, config_2_2, notTimeout),
            Edge(config_2_2, config_2_3, notTimeout),
            Edge(config_2_3, config_2_4, notTimeout),
            Edge(config_2_4, config_2_5, notTimeout),

            Edge(config_3_1, config_3_2, notTimeout),
            Edge(config_3_2, config_3_3, notTimeout),
            Edge(config_3_3, config_3_4, notTimeout),
            Edge(config_3_4, config_3_5, notTimeout),
        )
        return STM(config_1_1, timeouts union solverExceptions)
    }

    val inProcess = HierarchicalNode("InProcess", getStm(true))
    val notInProcess = HierarchicalNode("NotInprocess", getStm(false))

    val fallbackEdge = Edge(inProcess, notInProcess, ExceptionTrigger(label = "Anything"))

    return STM(inProcess, setOf(fallbackEdge))
}

val stm = when (traitsTyped.arithmetic) {
    BitwiseOption.INTEGER -> integerStm()
    BitwiseOption.BITWISE -> bitwiseStm()
    BitwiseOption.BITWISE_FLOAT -> floatsStm()
}

stm.execute()
