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

import hu.bme.mit.theta.analysis.PartialOrd
import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.algorithm.ArgNode
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.algorithm.cegar.Abstractor
import hu.bme.mit.theta.analysis.algorithm.cegar.CegarChecker
import hu.bme.mit.theta.analysis.algorithm.cegar.Refiner
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.refinement.*
import hu.bme.mit.theta.analysis.runtimemonitor.CexMonitor
import hu.bme.mit.theta.analysis.runtimemonitor.MonitorCheckpoint
import hu.bme.mit.theta.analysis.waitlist.PriorityWaitlist
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.graphsolver.patterns.constraints.MCM
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.xcfa.analysis.*
import hu.bme.mit.theta.xcfa.analysis.por.XcfaDporLts
import hu.bme.mit.theta.xcfa.cli.params.*
import hu.bme.mit.theta.xcfa.cli.utils.getSolver
import hu.bme.mit.theta.xcfa.model.XCFA

fun getCegarChecker(xcfa: XCFA, mcm: MCM,
    config: XcfaConfig<*, *>,
    logger: Logger): SafetyChecker<XcfaState<*>, XcfaAction, XcfaPrec<*>> {
    val cegarConfig = config.backendConfig.specConfig as CegarConfig
    val abstractionSolverFactory: SolverFactory = getSolver(cegarConfig.abstractorConfig.abstractionSolver,
        cegarConfig.abstractorConfig.validateAbstractionSolver)
    val refinementSolverFactory: SolverFactory = getSolver(cegarConfig.refinerConfig.refinementSolver,
        cegarConfig.refinerConfig.validateRefinementSolver)

    val ignoredVarRegistry = mutableMapOf<Decl<out Type>, MutableSet<ExprState>>()

    val lts = cegarConfig.coi.getLts(xcfa, ignoredVarRegistry, cegarConfig.porLevel)
    val waitlist = if (cegarConfig.porLevel.isDynamic) {
        (cegarConfig.coi.porLts as XcfaDporLts).waitlist
    } else {
        PriorityWaitlist.create<ArgNode<out XcfaState<out ExprState>, XcfaAction>>(
            cegarConfig.abstractorConfig.search.getComp(xcfa))
    }

    val abstractionSolverInstance = abstractionSolverFactory.createSolver()
    val globalStatePartialOrd: PartialOrd<out ExprState> = cegarConfig.abstractorConfig.domain.partialOrd(
        abstractionSolverInstance)
    val corePartialOrd: PartialOrd<out XcfaState<out ExprState>> =
        if (xcfa.isInlined) getPartialOrder(globalStatePartialOrd)
        else getStackPartialOrder(globalStatePartialOrd)
    val abstractor: Abstractor<ExprState, ExprAction, Prec> = cegarConfig.abstractorConfig.domain.abstractor(
        xcfa,
        abstractionSolverInstance,
        cegarConfig.abstractorConfig.maxEnum,
        waitlist,
        cegarConfig.refinerConfig.refinement.stopCriterion,
        logger,
        lts,
        config.inputConfig.property,
        if (cegarConfig.porLevel.isDynamic) {
            XcfaDporLts.getPartialOrder(corePartialOrd)
        } else {
            corePartialOrd
        }
    ) as Abstractor<ExprState, ExprAction, Prec>

    val ref: ExprTraceChecker<Refutation> =
        cegarConfig.refinerConfig.refinement.refiner(refinementSolverFactory, cegarConfig.cexMonitor)
            as ExprTraceChecker<Refutation>
    val precRefiner: PrecRefiner<ExprState, ExprAction, Prec, Refutation> =
        cegarConfig.abstractorConfig.domain.itpPrecRefiner(cegarConfig.refinerConfig.exprSplitter.exprSplitter)
            as PrecRefiner<ExprState, ExprAction, Prec, Refutation>
    val atomicNodePruner: NodePruner<ExprState, ExprAction> = cegarConfig.abstractorConfig.domain.nodePruner as NodePruner<ExprState, ExprAction>
    val refiner: Refiner<ExprState, ExprAction, Prec> =
        if (cegarConfig.refinerConfig.refinement == Refinement.MULTI_SEQ)
            if (cegarConfig.porLevel == POR.AASPOR)
                MultiExprTraceRefiner.create(ref, precRefiner, cegarConfig.refinerConfig.pruneStrategy, logger,
                    atomicNodePruner)
            else
                MultiExprTraceRefiner.create(ref, precRefiner, cegarConfig.refinerConfig.pruneStrategy, logger)
        else
            if (cegarConfig.porLevel == POR.AASPOR)
                XcfaSingleExprTraceRefiner.create(ref, precRefiner, cegarConfig.refinerConfig.pruneStrategy, logger,
                    atomicNodePruner)
            else
                XcfaSingleExprTraceRefiner.create(ref, precRefiner, cegarConfig.refinerConfig.pruneStrategy, logger)

    val cegarChecker = if (cegarConfig.porLevel == POR.AASPOR)
        CegarChecker.create(
            abstractor,
            AasporRefiner.create(refiner, cegarConfig.refinerConfig.pruneStrategy, ignoredVarRegistry),
            logger
        )
    else
        CegarChecker.create(abstractor, refiner, logger)

    // initialize monitors
    MonitorCheckpoint.reset()
    if (cegarConfig.cexMonitor == CexMonitorOptions.CHECK) {
        val cm = CexMonitor(logger, cegarChecker.arg)
        MonitorCheckpoint.register(cm, "CegarChecker.unsafeARG")
    }

    return object : SafetyChecker<XcfaState<*>, XcfaAction, XcfaPrec<*>> {
        override fun check(prec: XcfaPrec<*>?): SafetyResult<XcfaState<*>, XcfaAction> {
            return cegarChecker.check(prec) as SafetyResult<XcfaState<*>, XcfaAction>
        }

        override fun check(): SafetyResult<XcfaState<*>, XcfaAction> {
            return check(cegarConfig.abstractorConfig.domain.initPrec(xcfa, cegarConfig.initPrec))
        }
    }
}