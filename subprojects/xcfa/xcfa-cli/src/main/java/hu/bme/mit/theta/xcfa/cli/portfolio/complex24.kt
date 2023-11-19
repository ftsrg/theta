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

package hu.bme.mit.theta.xcfa.cli.portfolio

import hu.bme.mit.theta.analysis.expr.refinement.PruneStrategy
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.grammar.preprocess.ArithmeticTrait
import hu.bme.mit.theta.xcfa.analysis.ErrorDetection
import hu.bme.mit.theta.xcfa.cli.*
import hu.bme.mit.theta.xcfa.model.XCFA

fun complexPortfolio24(
    xcfaTyped: XCFA,
    cFileNameTyped: String,
    loggerTyped: Logger,
    smtHomeTyped: String,
    traitsTyped: VerificationTraits,
    propertyTyped: ErrorDetection,
    parseContextTyped: ParseContext,
    debug: Boolean,
    argdebug: Boolean): STM {

    val checker = { p: Boolean, config: XcfaCegarConfig ->
        if (p)
            config.checkInProcess(xcfaTyped, smtHomeTyped, true, cFileNameTyped, loggerTyped, parseContextTyped,
                argdebug)()
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
        coi = ConeOfInfluenceMode.NO_COI,
        refinementSolver = "Z3",
        validateRefinementSolver = false,
        refinement = Refinement.SEQ_ITP,
        exprSplitter = ExprSplitterOptions.WHOLE,
        pruneStrategy = PruneStrategy.FULL,
        cexMonitor = CexMonitorOptions.CHECK,
        timeoutMs = 0
    )

    if (traitsTyped.multithreaded) {
        baseConfig = baseConfig.copy(search = Search.DFS, porLevel = POR.AASPOR, pruneStrategy = PruneStrategy.LAZY,
            coi = ConeOfInfluenceMode.COI)

        if (propertyTyped == ErrorDetection.DATA_RACE) {
            baseConfig = baseConfig.copy(porLevel = POR.SPOR)
        }
    }
    val timeoutTrigger = ExceptionTrigger(
        ErrorCodeException(ExitCodes.TIMEOUT.code),
        ErrorCodeException(ExitCodes.VERIFICATION_STUCK.code),
        ErrorCodeException(ExitCodes.OUT_OF_MEMORY.code),
        ErrorCodeException(ExitCodes.GENERIC_ERROR.code),
        label = "TimeoutOrGenericError"
    )

    val timeoutOrSolverError = ExceptionTrigger(
        ErrorCodeException(ExitCodes.SOLVER_ERROR.code),
        ErrorCodeException(ExitCodes.TIMEOUT.code),
        ErrorCodeException(ExitCodes.VERIFICATION_STUCK.code),
        ErrorCodeException(ExitCodes.OUT_OF_MEMORY.code),
        ErrorCodeException(ExitCodes.GENERIC_ERROR.code),
        label = "TimeoutOrSolverError"
    )

    val solverError = ExceptionTrigger(
        ErrorCodeException(ExitCodes.SOLVER_ERROR.code),
        ErrorCodeException(ExitCodes.VERIFICATION_STUCK.code),
        label = "SolverError"
    )

    val anyError = ExceptionTrigger(label = "Anything")

    fun getStm(trait: ArithmeticTrait, inProcess: Boolean): STM {
        val edges = LinkedHashSet<Edge>()
        val config_BITWISE_EXPL_NWT_IT_WP_cvc5 = ConfigNode("BITWISE_EXPL_NWT_IT_WP_cvc5:1.0.8-$inProcess",
            baseConfig.copy(
                domain = Domain.EXPL,
                abstractionSolver = "cvc5:1.0.8",
                refinementSolver = "cvc5:1.0.8",
                refinement = Refinement.NWT_IT_WP,
                timeoutMs = 100000
            ), checker, inProcess)
        val config_BITWISE_EXPL_NWT_IT_WP_Z3 = ConfigNode("BITWISE_EXPL_NWT_IT_WP_Z3-$inProcess", baseConfig.copy(
            domain = Domain.EXPL,
            abstractionSolver = "Z3",
            refinementSolver = "Z3",
            refinement = Refinement.NWT_IT_WP,
            timeoutMs = 100000
        ), checker, inProcess)
        edges.add(Edge(config_BITWISE_EXPL_NWT_IT_WP_cvc5, config_BITWISE_EXPL_NWT_IT_WP_Z3, solverError))
        val config_BITWISE_EXPL_NWT_IT_WP_mathsat = ConfigNode("BITWISE_EXPL_NWT_IT_WP_mathsat:5.6.10-$inProcess",
            baseConfig.copy(
                domain = Domain.EXPL,
                abstractionSolver = "mathsat:5.6.10",
                refinementSolver = "mathsat:5.6.10",
                refinement = Refinement.NWT_IT_WP,
                timeoutMs = 100000
            ), checker, inProcess)
        edges.add(Edge(config_BITWISE_EXPL_NWT_IT_WP_Z3, config_BITWISE_EXPL_NWT_IT_WP_mathsat, solverError))
        val config_BITWISE_PRED_CART_SEQ_ITP_mathsat = ConfigNode("BITWISE_PRED_CART_SEQ_ITP_mathsat:5.6.10-$inProcess",
            baseConfig.copy(
                domain = Domain.PRED_CART,
                abstractionSolver = "mathsat:5.6.10",
                refinementSolver = "mathsat:5.6.10",
                refinement = Refinement.SEQ_ITP,
                timeoutMs = 0
            ), checker, inProcess)
        edges.add(Edge(config_BITWISE_EXPL_NWT_IT_WP_cvc5, config_BITWISE_PRED_CART_SEQ_ITP_mathsat,
            if (inProcess) timeoutTrigger else anyError))
        edges.add(Edge(config_BITWISE_EXPL_NWT_IT_WP_Z3, config_BITWISE_PRED_CART_SEQ_ITP_mathsat,
            if (inProcess) timeoutTrigger else anyError))
        edges.add(Edge(config_BITWISE_EXPL_NWT_IT_WP_mathsat, config_BITWISE_PRED_CART_SEQ_ITP_mathsat,
            if (inProcess) timeoutOrSolverError else anyError))
        val config_BITWISE_PRED_CART_SEQ_ITP_cvc5 = ConfigNode("BITWISE_PRED_CART_SEQ_ITP_cvc5:1.0.8-$inProcess",
            baseConfig.copy(
                domain = Domain.PRED_CART,
                abstractionSolver = "cvc5:1.0.8",
                refinementSolver = "cvc5:1.0.8",
                refinement = Refinement.SEQ_ITP,
                timeoutMs = 0
            ), checker, inProcess)
        edges.add(Edge(config_BITWISE_PRED_CART_SEQ_ITP_mathsat, config_BITWISE_PRED_CART_SEQ_ITP_cvc5, solverError))
        val config_BITWISE_EXPL_SEQ_ITP_mathsat = ConfigNode("BITWISE_EXPL_SEQ_ITP_mathsat:5.6.10-$inProcess",
            baseConfig.copy(
                domain = Domain.EXPL,
                abstractionSolver = "mathsat:5.6.10",
                refinementSolver = "mathsat:5.6.10",
                refinement = Refinement.SEQ_ITP,
                timeoutMs = 0
            ), checker, inProcess)
        edges.add(Edge(config_BITWISE_PRED_CART_SEQ_ITP_mathsat, config_BITWISE_EXPL_SEQ_ITP_mathsat,
            if (inProcess) timeoutTrigger else anyError))
        edges.add(Edge(config_BITWISE_PRED_CART_SEQ_ITP_cvc5, config_BITWISE_EXPL_SEQ_ITP_mathsat,
            if (inProcess) timeoutOrSolverError else anyError))
        val config_BITWISE_EXPL_SEQ_ITP_cvc5 = ConfigNode("BITWISE_EXPL_SEQ_ITP_cvc5:1.0.8-$inProcess", baseConfig.copy(
            domain = Domain.EXPL,
            abstractionSolver = "cvc5:1.0.8",
            refinementSolver = "cvc5:1.0.8",
            refinement = Refinement.SEQ_ITP,
            timeoutMs = 0
        ), checker, inProcess)
        edges.add(Edge(config_BITWISE_EXPL_SEQ_ITP_mathsat, config_BITWISE_EXPL_SEQ_ITP_cvc5, solverError))
        val config_FLOAT_EXPL_NWT_IT_WP_cvc5 = ConfigNode("FLOAT_EXPL_NWT_IT_WP_cvc5:1.0.8-$inProcess", baseConfig.copy(
            domain = Domain.EXPL,
            abstractionSolver = "cvc5:1.0.8",
            refinementSolver = "cvc5:1.0.8",
            refinement = Refinement.NWT_IT_WP,
            timeoutMs = 200000
        ), checker, inProcess)
        val config_FLOAT_EXPL_NWT_IT_WP_Z3 = ConfigNode("FLOAT_EXPL_NWT_IT_WP_Z3-$inProcess", baseConfig.copy(
            domain = Domain.EXPL,
            abstractionSolver = "Z3",
            refinementSolver = "Z3",
            refinement = Refinement.NWT_IT_WP,
            timeoutMs = 200000
        ), checker, inProcess)
        edges.add(Edge(config_FLOAT_EXPL_NWT_IT_WP_cvc5, config_FLOAT_EXPL_NWT_IT_WP_Z3, solverError))
        val config_FLOAT_EXPL_NWT_IT_WP_mathsat = ConfigNode("FLOAT_EXPL_NWT_IT_WP_mathsat:5.6.10-$inProcess",
            baseConfig.copy(
                domain = Domain.EXPL,
                abstractionSolver = "mathsat:5.6.10",
                refinementSolver = "mathsat:5.6.10", validateRefinementSolver = true,
                refinement = Refinement.NWT_IT_WP,
                timeoutMs = 200000
            ), checker, inProcess)
        edges.add(Edge(config_FLOAT_EXPL_NWT_IT_WP_Z3, config_FLOAT_EXPL_NWT_IT_WP_mathsat, solverError))
        val config_FLOAT_PRED_CART_SEQ_ITP_mathsat = ConfigNode("FLOAT_PRED_CART_SEQ_ITP_mathsat:5.6.10-$inProcess",
            baseConfig.copy(
                domain = Domain.PRED_CART,
                abstractionSolver = "mathsat:5.6.10",
                refinementSolver = "mathsat:5.6.10", validateRefinementSolver = true,
                refinement = Refinement.SEQ_ITP,
                timeoutMs = 0
            ), checker, inProcess)
        edges.add(Edge(config_FLOAT_EXPL_NWT_IT_WP_cvc5, config_FLOAT_PRED_CART_SEQ_ITP_mathsat,
            if (inProcess) timeoutTrigger else anyError))
        edges.add(Edge(config_FLOAT_EXPL_NWT_IT_WP_Z3, config_FLOAT_PRED_CART_SEQ_ITP_mathsat,
            if (inProcess) timeoutTrigger else anyError))
        edges.add(Edge(config_FLOAT_EXPL_NWT_IT_WP_mathsat, config_FLOAT_PRED_CART_SEQ_ITP_mathsat,
            if (inProcess) timeoutOrSolverError else anyError))
        val config_FLOAT_PRED_CART_SEQ_ITP_cvc5 = ConfigNode("FLOAT_PRED_CART_SEQ_ITP_cvc5:1.0.8-$inProcess",
            baseConfig.copy(
                domain = Domain.PRED_CART,
                abstractionSolver = "cvc5:1.0.8",
                refinementSolver = "cvc5:1.0.8",
                refinement = Refinement.SEQ_ITP,
                timeoutMs = 0
            ), checker, inProcess)
        edges.add(Edge(config_FLOAT_PRED_CART_SEQ_ITP_mathsat, config_FLOAT_PRED_CART_SEQ_ITP_cvc5, solverError))
        val config_FLOAT_EXPL_SEQ_ITP_mathsat = ConfigNode("FLOAT_EXPL_SEQ_ITP_mathsat:5.6.10-$inProcess",
            baseConfig.copy(
                domain = Domain.EXPL,
                abstractionSolver = "mathsat:5.6.10",
                refinementSolver = "mathsat:5.6.10", validateRefinementSolver = true,
                refinement = Refinement.SEQ_ITP,
                timeoutMs = 0
            ), checker, inProcess)
        edges.add(Edge(config_FLOAT_PRED_CART_SEQ_ITP_mathsat, config_FLOAT_EXPL_SEQ_ITP_mathsat,
            if (inProcess) timeoutTrigger else anyError))
        edges.add(Edge(config_FLOAT_PRED_CART_SEQ_ITP_cvc5, config_FLOAT_EXPL_SEQ_ITP_mathsat,
            if (inProcess) timeoutOrSolverError else anyError))
        val config_FLOAT_EXPL_SEQ_ITP_cvc5 = ConfigNode("FLOAT_EXPL_SEQ_ITP_cvc5:1.0.8-$inProcess", baseConfig.copy(
            domain = Domain.EXPL,
            abstractionSolver = "cvc5:1.0.8",
            refinementSolver = "cvc5:1.0.8",
            refinement = Refinement.SEQ_ITP,
            timeoutMs = 0
        ), checker, inProcess)
        edges.add(Edge(config_FLOAT_EXPL_SEQ_ITP_mathsat, config_FLOAT_EXPL_SEQ_ITP_cvc5, solverError))
        val config_LIN_INT_EXPL_NWT_IT_WP_mathsat = ConfigNode("LIN_INT_EXPL_NWT_IT_WP_mathsat:5.6.10-$inProcess",
            baseConfig.copy(
                domain = Domain.EXPL,
                abstractionSolver = "mathsat:5.6.10",
                refinementSolver = "mathsat:5.6.10",
                refinement = Refinement.NWT_IT_WP,
                timeoutMs = 100000
            ), checker, inProcess)
        val config_LIN_INT_EXPL_NWT_IT_WP_Z3 = ConfigNode("LIN_INT_EXPL_NWT_IT_WP_Z3-$inProcess", baseConfig.copy(
            domain = Domain.EXPL,
            abstractionSolver = "Z3",
            refinementSolver = "Z3",
            refinement = Refinement.NWT_IT_WP,
            timeoutMs = 100000
        ), checker, inProcess)
        edges.add(Edge(config_LIN_INT_EXPL_NWT_IT_WP_mathsat, config_LIN_INT_EXPL_NWT_IT_WP_Z3, solverError))
        val config_LIN_INT_EXPL_SEQ_ITP_Z3 = ConfigNode("LIN_INT_EXPL_SEQ_ITP_Z3-$inProcess", baseConfig.copy(
            domain = Domain.EXPL,
            abstractionSolver = "Z3",
            refinementSolver = "Z3",
            refinement = Refinement.SEQ_ITP,
            timeoutMs = 300000
        ), checker, inProcess)
        edges.add(Edge(config_LIN_INT_EXPL_NWT_IT_WP_mathsat, config_LIN_INT_EXPL_SEQ_ITP_Z3,
            if (inProcess) timeoutTrigger else anyError))
        edges.add(Edge(config_LIN_INT_EXPL_NWT_IT_WP_Z3, config_LIN_INT_EXPL_SEQ_ITP_Z3,
            if (inProcess) timeoutOrSolverError else anyError))
        val config_LIN_INT_EXPL_SEQ_ITP_mathsat = ConfigNode("LIN_INT_EXPL_SEQ_ITP_mathsat:5.6.10-$inProcess",
            baseConfig.copy(
            domain = Domain.EXPL,
            abstractionSolver = "mathsat:5.6.10",
            refinementSolver = "mathsat:5.6.10",
            refinement = Refinement.SEQ_ITP,
            timeoutMs = 300000
        ), checker, inProcess)
        edges.add(Edge(config_LIN_INT_EXPL_SEQ_ITP_Z3, config_LIN_INT_EXPL_SEQ_ITP_mathsat, solverError))
        val config_LIN_INT_PRED_CART_SEQ_ITP_Z3 = ConfigNode("LIN_INT_PRED_CART_SEQ_ITP_Z3-$inProcess", baseConfig.copy(
            domain = Domain.PRED_CART,
            abstractionSolver = "Z3",
            refinementSolver = "Z3",
            refinement = Refinement.SEQ_ITP,
            timeoutMs = 0
        ), checker, inProcess)
        edges.add(Edge(config_LIN_INT_EXPL_SEQ_ITP_Z3, config_LIN_INT_PRED_CART_SEQ_ITP_Z3,
            if (inProcess) timeoutTrigger else anyError))
        edges.add(Edge(config_LIN_INT_EXPL_SEQ_ITP_mathsat, config_LIN_INT_PRED_CART_SEQ_ITP_Z3,
            if (inProcess) timeoutOrSolverError else anyError))
        val config_LIN_INT_PRED_CART_SEQ_ITP_mathsat = ConfigNode("LIN_INT_PRED_CART_SEQ_ITP_mathsat:5.6.10-$inProcess",
            baseConfig.copy(
                domain = Domain.PRED_CART,
                abstractionSolver = "mathsat:5.6.10",
                refinementSolver = "mathsat:5.6.10",
                refinement = Refinement.SEQ_ITP,
                timeoutMs = 0
            ), checker, inProcess)
        edges.add(Edge(config_LIN_INT_PRED_CART_SEQ_ITP_Z3, config_LIN_INT_PRED_CART_SEQ_ITP_mathsat, solverError))
        val config_LIN_INT_PRED_CART_SEQ_ITP_z3 = ConfigNode("LIN_INT_PRED_CART_SEQ_ITP_z3:4.12.2-$inProcess",
            baseConfig.copy(
            domain = Domain.PRED_CART,
            abstractionSolver = "z3:4.12.2",
            refinementSolver = "z3:4.12.2",
            refinement = Refinement.SEQ_ITP,
            timeoutMs = 0
        ), checker, inProcess)
        edges.add(Edge(config_LIN_INT_PRED_CART_SEQ_ITP_mathsat, config_LIN_INT_PRED_CART_SEQ_ITP_z3, solverError))
        val config_NONLIN_INT_EXPL_NWT_IT_WP_Z3 = ConfigNode("NONLIN_INT_EXPL_NWT_IT_WP_Z3-$inProcess", baseConfig.copy(
            domain = Domain.EXPL,
            abstractionSolver = "Z3",
            refinementSolver = "Z3",
            refinement = Refinement.NWT_IT_WP,
            timeoutMs = 100000
        ), checker, inProcess)
        val config_NONLIN_INT_EXPL_NWT_IT_WP_mathsat = ConfigNode("NONLIN_INT_EXPL_NWT_IT_WP_mathsat:5.6.10-$inProcess",
            baseConfig.copy(
                domain = Domain.EXPL,
                abstractionSolver = "mathsat:5.6.10",
                refinementSolver = "mathsat:5.6.10",
                refinement = Refinement.NWT_IT_WP,
                timeoutMs = 100000
            ), checker, inProcess)
        edges.add(Edge(config_NONLIN_INT_EXPL_NWT_IT_WP_Z3, config_NONLIN_INT_EXPL_NWT_IT_WP_mathsat, solverError))
        val config_NONLIN_INT_EXPL_SEQ_ITP_Z3 = ConfigNode("NONLIN_INT_EXPL_SEQ_ITP_Z3-$inProcess", baseConfig.copy(
            domain = Domain.EXPL,
            abstractionSolver = "Z3",
            refinementSolver = "Z3",
            refinement = Refinement.SEQ_ITP,
            timeoutMs = 100000
        ), checker, inProcess)
        edges.add(Edge(config_NONLIN_INT_EXPL_NWT_IT_WP_Z3, config_NONLIN_INT_EXPL_SEQ_ITP_Z3,
            if (inProcess) timeoutTrigger else anyError))
        edges.add(Edge(config_NONLIN_INT_EXPL_NWT_IT_WP_mathsat, config_NONLIN_INT_EXPL_SEQ_ITP_Z3,
            if (inProcess) timeoutOrSolverError else anyError))
        val config_NONLIN_INT_EXPL_SEQ_ITP_mathsat = ConfigNode("NONLIN_INT_EXPL_SEQ_ITP_mathsat:5.6.10-$inProcess",
            baseConfig.copy(
                domain = Domain.EXPL,
                abstractionSolver = "mathsat:5.6.10",
                refinementSolver = "mathsat:5.6.10",
                refinement = Refinement.SEQ_ITP,
                timeoutMs = 200000
            ), checker, inProcess)
        edges.add(Edge(config_NONLIN_INT_EXPL_SEQ_ITP_Z3, config_NONLIN_INT_EXPL_SEQ_ITP_mathsat,
            if (inProcess) timeoutOrSolverError else anyError))
        val config_NONLIN_INT_PRED_CART_SEQ_ITP_mathsat = ConfigNode(
            "NONLIN_INT_PRED_CART_SEQ_ITP_mathsat:5.6.10-$inProcess", baseConfig.copy(
            domain = Domain.PRED_CART,
            abstractionSolver = "mathsat:5.6.10",
            refinementSolver = "mathsat:5.6.10",
            refinement = Refinement.SEQ_ITP,
            timeoutMs = 0
        ), checker, inProcess)
        edges.add(Edge(config_NONLIN_INT_EXPL_SEQ_ITP_mathsat, config_NONLIN_INT_PRED_CART_SEQ_ITP_mathsat,
            if (inProcess) timeoutOrSolverError else anyError))
        val config_NONLIN_INT_EXPL_NWT_IT_WP_cvc5 = ConfigNode("NONLIN_INT_EXPL_NWT_IT_WP_cvc5:1.0.8-$inProcess",
            baseConfig.copy(
                domain = Domain.EXPL,
                abstractionSolver = "cvc5:1.0.8",
                refinementSolver = "cvc5:1.0.8",
                refinement = Refinement.NWT_IT_WP,
                timeoutMs = 0
            ), checker, inProcess)
        edges.add(Edge(config_NONLIN_INT_PRED_CART_SEQ_ITP_mathsat, config_NONLIN_INT_EXPL_NWT_IT_WP_cvc5,
            if (inProcess) timeoutOrSolverError else anyError))
        val config_ARR_EXPL_NWT_IT_WP_cvc5 = ConfigNode("ARR_EXPL_NWT_IT_WP_cvc5:1.0.8-$inProcess", baseConfig.copy(
            domain = Domain.EXPL,
            abstractionSolver = "cvc5:1.0.8",
            refinementSolver = "cvc5:1.0.8",
            refinement = Refinement.NWT_IT_WP,
            timeoutMs = 100000
        ), checker, inProcess)
        val config_ARR_EXPL_NWT_IT_WP_Z3 = ConfigNode("ARR_EXPL_NWT_IT_WP_Z3-$inProcess", baseConfig.copy(
            domain = Domain.EXPL,
            abstractionSolver = "Z3",
            refinementSolver = "Z3",
            refinement = Refinement.NWT_IT_WP,
            timeoutMs = 100000
        ), checker, inProcess)
        edges.add(Edge(config_ARR_EXPL_NWT_IT_WP_cvc5, config_ARR_EXPL_NWT_IT_WP_Z3, solverError))
        val config_ARR_PRED_CART_SEQ_ITP_Z3 = ConfigNode("ARR_PRED_CART_SEQ_ITP_Z3-$inProcess", baseConfig.copy(
            domain = Domain.PRED_CART,
            abstractionSolver = "Z3",
            refinementSolver = "Z3",
            refinement = Refinement.SEQ_ITP,
            timeoutMs = 300000
        ), checker, inProcess)
        edges.add(Edge(config_ARR_EXPL_NWT_IT_WP_cvc5, config_ARR_PRED_CART_SEQ_ITP_Z3,
            if (inProcess) timeoutTrigger else anyError))
        edges.add(Edge(config_ARR_EXPL_NWT_IT_WP_Z3, config_ARR_PRED_CART_SEQ_ITP_Z3,
            if (inProcess) timeoutOrSolverError else anyError))
        val config_ARR_PRED_CART_SEQ_ITP_z3 = ConfigNode("ARR_PRED_CART_SEQ_ITP_z3:4.12.2-$inProcess", baseConfig.copy(
            domain = Domain.PRED_CART,
            abstractionSolver = "z3:4.12.2",
            refinementSolver = "z3:4.12.2",
            refinement = Refinement.SEQ_ITP,
            timeoutMs = 300000
        ), checker, inProcess)
        edges.add(Edge(config_ARR_PRED_CART_SEQ_ITP_Z3, config_ARR_PRED_CART_SEQ_ITP_z3, solverError))
        val config_ARR_PRED_CART_SEQ_ITP_princess = ConfigNode("ARR_PRED_CART_SEQ_ITP_princess:2023-06-19-$inProcess",
            baseConfig.copy(
                domain = Domain.PRED_CART,
                abstractionSolver = "princess:2023-06-19",
                refinementSolver = "princess:2023-06-19",
                refinement = Refinement.SEQ_ITP,
                timeoutMs = 500000
            ), checker, inProcess)
        edges.add(Edge(config_ARR_PRED_CART_SEQ_ITP_Z3, config_ARR_PRED_CART_SEQ_ITP_princess,
            if (inProcess) timeoutTrigger else anyError))
        edges.add(Edge(config_ARR_PRED_CART_SEQ_ITP_z3, config_ARR_PRED_CART_SEQ_ITP_princess,
            if (inProcess) timeoutOrSolverError else anyError))
        val config_ARR_PRED_CART_SEQ_ITP_cvc5 = ConfigNode("ARR_PRED_CART_SEQ_ITP_cvc5:1.0.8-$inProcess",
            baseConfig.copy(
                domain = Domain.PRED_CART,
                abstractionSolver = "cvc5:1.0.8",
                refinementSolver = "cvc5:1.0.8",
                refinement = Refinement.SEQ_ITP,
                timeoutMs = 500000
            ), checker, inProcess)
        edges.add(Edge(config_ARR_PRED_CART_SEQ_ITP_princess, config_ARR_PRED_CART_SEQ_ITP_cvc5, solverError))
        if (trait == ArithmeticTrait.BITWISE) {
            return STM(config_BITWISE_EXPL_NWT_IT_WP_cvc5, edges)
        }

        if (trait == ArithmeticTrait.FLOAT) {
            return STM(config_FLOAT_EXPL_NWT_IT_WP_cvc5, edges)
        }

        if (trait == ArithmeticTrait.LIN_INT) {
            return STM(config_LIN_INT_EXPL_NWT_IT_WP_mathsat, edges)
        }

        if (trait == ArithmeticTrait.NONLIN_INT) {
            return STM(config_NONLIN_INT_EXPL_NWT_IT_WP_Z3, edges)
        }

        if (trait == ArithmeticTrait.ARR) {
            return STM(config_ARR_EXPL_NWT_IT_WP_cvc5, edges)
        }

        error("Unknown trait!")
    }

    val mainTrait =
        if (ArithmeticTrait.FLOAT in traitsTyped.arithmeticTraits) ArithmeticTrait.FLOAT
        else if (ArithmeticTrait.ARR in traitsTyped.arithmeticTraits) ArithmeticTrait.ARR
        else if (ArithmeticTrait.BITWISE in traitsTyped.arithmeticTraits) ArithmeticTrait.BITWISE
        else if (ArithmeticTrait.NONLIN_INT in traitsTyped.arithmeticTraits) ArithmeticTrait.NONLIN_INT
        else ArithmeticTrait.LIN_INT

    val inProcess = HierarchicalNode("InProcess", getStm(mainTrait, true))
    val notInProcess = HierarchicalNode("NotInprocess", getStm(mainTrait, false))

    val fallbackEdge = Edge(inProcess, notInProcess, ExceptionTrigger(label = "Anything"))

    return if (debug) getStm(mainTrait, false) else STM(inProcess, setOf(fallbackEdge))
}