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

import com.google.common.base.Preconditions.checkState
import hu.bme.mit.theta.analysis.PartialOrd
import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.algorithm.arg.ARG
import hu.bme.mit.theta.analysis.algorithm.arg.ArgNode
import hu.bme.mit.theta.analysis.algorithm.asg.ASG
import hu.bme.mit.theta.analysis.algorithm.asg.ASGTrace
import hu.bme.mit.theta.analysis.algorithm.cegar.CegarChecker
import hu.bme.mit.theta.analysis.algorithm.loopchecker.AcceptancePredicate
import hu.bme.mit.theta.analysis.algorithm.loopchecker.abstraction.LoopCheckerSearchStrategy
import hu.bme.mit.theta.analysis.algorithm.loopchecker.refinement.ASGTraceCheckerStrategy
import hu.bme.mit.theta.analysis.algorithm.loopchecker.refinement.SingleASGTraceRefiner
import hu.bme.mit.theta.analysis.expl.ExplPrec
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expl.ItpRefToExplPrec
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.refinement.*
import hu.bme.mit.theta.analysis.ptr.ItpRefToPtrPrec
import hu.bme.mit.theta.analysis.ptr.PtrPrec
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.analysis.utils.AsgVisualizer
import hu.bme.mit.theta.analysis.waitlist.PriorityWaitlist
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.graphsolver.patterns.constraints.MCM
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.xcfa.analysis.*
import hu.bme.mit.theta.xcfa.analysis.por.XcfaDporLts
import hu.bme.mit.theta.xcfa.cli.params.*
import hu.bme.mit.theta.xcfa.cli.utils.getSolver
import hu.bme.mit.theta.xcfa.model.XCFA
import java.util.*
import java.util.function.Predicate

fun getCegarLassoChecker(
  xcfa: XCFA,
  mcm: MCM,
  config: XcfaConfig<*, *>,
  logger: Logger,
): SafetyChecker<
  ARG<XcfaState<*>, XcfaAction>,
  Trace<XcfaState<PtrState<*>>, XcfaAction>,
  XcfaPrec<PtrPrec<ExplPrec>>,
> {
  checkState(
    config.inputConfig.property == ErrorDetection.TERMINATION,
    "Lasso checker should be used for checking termination!",
  )

  val cegarConfig = config.backendConfig.specConfig as CegarConfig
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

  val por =
    if (cegarConfig.porLevel.isDynamic) {
      XcfaDporLts.getPartialOrder(corePartialOrd)
    } else {
      corePartialOrd
    }
  // TODO not hardcoded parameters
  // TODO partial orders nicely
  val analysis =
    ExplXcfaAnalysis(
      xcfa,
      abstractionSolverInstance,
      10,
      por as PartialOrd<XcfaState<PtrState<ExplState>>>,
      cegarConfig.abstractorConfig.havocMemory,
    )

  val statePredicate: Predicate<XcfaState<PtrState<ExplState>>?> =
    Predicate { xcfaState: XcfaState<PtrState<ExplState>>? ->
      if (xcfaState!!.sGlobal.innerState.isBottom) {
        false
      } else {
        try {
          val valuation = xcfaState!!.sGlobal.innerState.`val`
          val prop =
            ExprUtils.changeDecls(
              xcfa.initProcedures[0].first.prop,
              xcfaState.processes.getOrDefault(0, null)?.varLookup?.getOrNull(0)
                ?: emptyMap<VarDecl<*>, VarDecl<*>>(),
            )
          prop.eval(valuation).equals(True())
        } catch (e: NoSuchElementException) {
          false
        }
      }
    }
  val target =
    AcceptancePredicate<XcfaState<PtrState<ExplState>>, XcfaAction>(statePredicate::test, Unit)

  val searchStrategy = LoopCheckerSearchStrategy.NDFS
  val abstractor = getExplXcfaASGAbstractor(analysis, logger, lts, searchStrategy, target)

  val asg = ASG(target)

  val ref: ExprTraceChecker<Refutation> =
    cegarConfig.refinerConfig.refinement.refiner(refinementSolverFactory, cegarConfig.cexMonitor)
      as ExprTraceChecker<Refutation>
  /*val precRefiner: PrecRefiner<ExprState, ExprAction, Prec, Refutation> =
  cegarConfig.abstractorConfig.domain.itpPrecRefiner(
    cegarConfig.refinerConfig.exprSplitter.exprSplitter
  ) as PrecRefiner<ExprState, ExprAction, Prec, Refutation>*/
  val atomicNodePruner: NodePruner<ExprState, ExprAction> =
    cegarConfig.abstractorConfig.domain.nodePruner as NodePruner<ExprState, ExprAction>

  ////////////////////////////////

  /*
  val refToPrec: RefutationToPrec<PredPrec, ItpRefutation> =
    ItpRefToPredPrec(ExprSplitters.atoms())
  val cfaRefToPrec: RefutationToGlobalCfaPrec<PredPrec, ItpRefutation> =
    RefutationToGlobalCfaPrec<PredPrec, ItpRefutation>(refToPrec, cfa.getInitLoc())
  */

  val traceCheckerStrategy = ASGTraceCheckerStrategy.DIRECT_REFINEMENT

  val precRefiner =
    XcfaPrecRefiner<PtrState<ExplState>, ExplPrec, ItpRefutation>(
      ItpRefToPtrPrec(ItpRefToExplPrec())
    )

  val refiner =
    SingleASGTraceRefiner(traceCheckerStrategy, refinementSolverFactory, precRefiner, logger)

  val cegarChecker:
    CegarChecker<
      XcfaPrec<PtrPrec<ExplPrec>>,
      ASG<XcfaState<PtrState<ExplState>>, XcfaAction>,
      ASGTrace<XcfaState<PtrState<ExplState>>, XcfaAction>,
    > =
    CegarChecker.create<
      XcfaPrec<PtrPrec<ExplPrec>>,
      ASG<XcfaState<PtrState<ExplState>>, XcfaAction>,
      ASGTrace<XcfaState<PtrState<ExplState>>, XcfaAction>,
    >(
      abstractor,
      refiner,
      logger,
      AsgVisualizer({ o: Any? -> Objects.toString(o) }, { o: Any? -> Objects.toString(o) }),
    )

  return object :
    SafetyChecker<
      ARG<XcfaState<*>, XcfaAction>,
      Trace<XcfaState<PtrState<*>>, XcfaAction>,
      XcfaPrec<PtrPrec<ExplPrec>>,
    > {
    override fun check(
      prec: XcfaPrec<PtrPrec<ExplPrec>>?
    ): SafetyResult<ARG<XcfaState<*>, XcfaAction>, Trace<XcfaState<PtrState<*>>, XcfaAction>> {
      return cegarChecker.check(prec)
        as SafetyResult<ARG<XcfaState<*>, XcfaAction>, Trace<XcfaState<PtrState<*>>, XcfaAction>>
    }

    override fun check():
      SafetyResult<ARG<XcfaState<*>, XcfaAction>, Trace<XcfaState<PtrState<*>>, XcfaAction>> {
      return check(Domain.EXPL.initPrec(xcfa, cegarConfig.initPrec) as XcfaPrec<PtrPrec<ExplPrec>>)
    }
  }
}
