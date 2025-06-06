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

import hu.bme.mit.theta.analysis.PartialOrd
import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.algorithm.arg.ArgNode
import hu.bme.mit.theta.analysis.algorithm.cegar.ArgAbstractor
import hu.bme.mit.theta.analysis.algorithm.cegar.ArgCegarChecker
import hu.bme.mit.theta.analysis.algorithm.cegar.ArgRefiner
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.refinement.*
import hu.bme.mit.theta.analysis.pred.PredState
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.analysis.runtimemonitor.CexMonitor
import hu.bme.mit.theta.analysis.runtimemonitor.MonitorCheckpoint
import hu.bme.mit.theta.analysis.waitlist.PriorityWaitlist
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.changeVars
import hu.bme.mit.theta.graphsolver.patterns.constraints.MCM
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.xcfa.analysis.*
import hu.bme.mit.theta.xcfa.analysis.por.XcfaDporLts
import hu.bme.mit.theta.xcfa.cli.params.*
import hu.bme.mit.theta.xcfa.cli.utils.LocationInvariants
import hu.bme.mit.theta.xcfa.cli.utils.getSolver
import hu.bme.mit.theta.xcfa.dereferences
import hu.bme.mit.theta.xcfa.model.XCFA

fun getCegarChecker(
  xcfa: XCFA,
  mcm: MCM,
  config: XcfaConfig<*, *>,
  logger: Logger,
): SafetyChecker<LocationInvariants, Trace<XcfaState<PtrState<*>>, XcfaAction>, XcfaPrec<*>> {
  val cegarConfig = config.backendConfig.specConfig as CegarConfig
  if (
    config.inputConfig.property == ErrorDetection.DATA_RACE &&
      xcfa.procedures.any { it.edges.any { it.label.dereferences.isNotEmpty() } }
  ) {
    throw RuntimeException("DATA_RACE cannot be checked when pointers exist in the file.")
  }
  val abstractionSolverFactory: SolverFactory =
    getSolver(
      cegarConfig.abstractorConfig.abstractionSolver,
      cegarConfig.abstractorConfig.validateAbstractionSolver,
    )
  val refinementSolverFactory: SolverFactory =
    getSolver(
      cegarConfig.refinerConfig.refinementSolver,
      cegarConfig.refinerConfig.validateRefinementSolver,
    )

  val ignoredVarRegistry = mutableMapOf<VarDecl<*>, MutableSet<ExprState>>()

  val lts = cegarConfig.coi.getLts(xcfa, ignoredVarRegistry, cegarConfig.porLevel)
  val waitlist =
    if (cegarConfig.porLevel.isDynamic) {
      (cegarConfig.coi.porLts as XcfaDporLts).waitlist
    } else {
      PriorityWaitlist.create<ArgNode<out XcfaState<PtrState<ExprState>>, XcfaAction>>(
        cegarConfig.abstractorConfig.search.getComp(xcfa)
      )
    }

  val abstractionSolverInstance = abstractionSolverFactory.createSolver()
  val globalStatePartialOrd: PartialOrd<PtrState<ExprState>> =
    cegarConfig.abstractorConfig.domain.partialOrd(abstractionSolverInstance)
      as PartialOrd<PtrState<ExprState>>
  val corePartialOrd: PartialOrd<XcfaState<PtrState<ExprState>>> =
    if (xcfa.isInlined) getPartialOrder(globalStatePartialOrd)
    else getStackPartialOrder(globalStatePartialOrd)
  val abstractor: ArgAbstractor<ExprState, ExprAction, Prec> =
    cegarConfig.abstractorConfig.domain.abstractor(
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
      },
      cegarConfig.abstractorConfig.havocMemory,
    ) as ArgAbstractor<ExprState, ExprAction, Prec>

  val ref: ExprTraceChecker<Refutation> =
    cegarConfig.refinerConfig.refinement.refiner(refinementSolverFactory, cegarConfig.cexMonitor)
      as ExprTraceChecker<Refutation>
  val precRefiner: PrecRefiner<ExprState, ExprAction, Prec, Refutation> =
    cegarConfig.abstractorConfig.domain.itpPrecRefiner(
      cegarConfig.refinerConfig.exprSplitter.exprSplitter
    ) as PrecRefiner<ExprState, ExprAction, Prec, Refutation>
  val atomicNodePruner: NodePruner<ExprState, ExprAction> =
    cegarConfig.abstractorConfig.domain.nodePruner as NodePruner<ExprState, ExprAction>
  val refiner: ArgRefiner<ExprState, ExprAction, Prec> =
    if (cegarConfig.refinerConfig.refinement == Refinement.MULTI_SEQ)
      if (cegarConfig.porLevel == POR.AASPOR)
        MultiExprTraceRefiner.create(
          ref,
          precRefiner,
          cegarConfig.refinerConfig.pruneStrategy,
          logger,
          atomicNodePruner,
        )
      else
        MultiExprTraceRefiner.create(
          ref,
          precRefiner,
          cegarConfig.refinerConfig.pruneStrategy,
          logger,
        )
    else if (cegarConfig.porLevel == POR.AASPOR)
      XcfaSingleExprTraceRefiner.create(
        ref,
        precRefiner,
        cegarConfig.refinerConfig.pruneStrategy,
        logger,
        atomicNodePruner,
      )
    else
      XcfaSingleExprTraceRefiner.create(
        ref,
        precRefiner,
        cegarConfig.refinerConfig.pruneStrategy,
        logger,
      )

  val cegarChecker =
    if (cegarConfig.porLevel == POR.AASPOR)
      ArgCegarChecker.create(
        abstractor,
        AasporRefiner.create(refiner, cegarConfig.refinerConfig.pruneStrategy, ignoredVarRegistry),
        logger,
      )
    else ArgCegarChecker.create(abstractor, refiner, logger)

  // initialize monitors
  MonitorCheckpoint.reset()
  if (cegarConfig.cexMonitor == CexMonitorOptions.CHECK) {
    val cm = CexMonitor(logger, cegarChecker.proof)
    MonitorCheckpoint.register(cm, "CegarChecker.unsafeARG")
  }

  return object :
    SafetyChecker<LocationInvariants, Trace<XcfaState<PtrState<*>>, XcfaAction>, XcfaPrec<*>> {
    override fun check(
      prec: XcfaPrec<*>?
    ): SafetyResult<LocationInvariants, Trace<XcfaState<PtrState<*>>, XcfaAction>> {
      val ret = cegarChecker.check(prec)
      if (ret.isSafe) {
        val arg = ret.asSafe().proof

        val locmap =
          xcfa.procedures
            .flatMap { it.locs }
            .associateWith { loc ->
              arg.nodes
                .filter {
                  (it.state as XcfaState<PtrState<*>>).processes.any { it.value.locs.peek() == loc }
                }
                .map {
                  (it.state as XcfaState<PtrState<*>>).sGlobal.innerState.let { s ->
                    val declMap =
                      (it.state as XcfaState<PtrState<*>>)
                        .processes
                        .map {
                          it.value.varLookup.reversed().reduce { a, b -> a + b }.reverseMapping()
                        }
                        .reduce { a, b -> a + b }
                    when (s) {
                      is ExplState -> {
                        if (s.isBottom) {
                          ExplState.bottom()
                        } else {
                          ExplState.of(s.`val`.changeVars(declMap))
                        }
                      }
                      is PredState -> {
                        PredState.of(s.preds.map { ExprUtils.changeDecls(it, declMap) })
                      }
                      else -> {
                        error("Unknown state: ${s}")
                      }
                    }
                  }
                }
                .toList()
            }

        return SafetyResult.safe(LocationInvariants(locmap))
      } else {
        return SafetyResult.unsafe(
          ret.asUnsafe().cex as Trace<XcfaState<PtrState<*>>, XcfaAction>,
          LocationInvariants(),
        )
      }
    }

    override fun check():
      SafetyResult<LocationInvariants, Trace<XcfaState<PtrState<*>>, XcfaAction>> {
      return check(cegarConfig.abstractorConfig.domain.initPrec(xcfa, cegarConfig.initPrec))
    }
  }
}
