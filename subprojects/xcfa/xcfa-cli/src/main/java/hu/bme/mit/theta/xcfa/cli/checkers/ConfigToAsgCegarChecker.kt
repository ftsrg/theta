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
import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.algorithm.asg.ASG
import hu.bme.mit.theta.analysis.algorithm.asg.ASGTrace
import hu.bme.mit.theta.analysis.algorithm.cegar.AsgCegarChecker
import hu.bme.mit.theta.analysis.algorithm.loopchecker.abstraction.ASGAbstractor
import hu.bme.mit.theta.analysis.algorithm.loopchecker.refinement.SingleASGTraceRefiner
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.ExprStatePredicate
import hu.bme.mit.theta.analysis.expr.refinement.*
import hu.bme.mit.theta.analysis.pred.PredState
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.graphsolver.patterns.constraints.MCM
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.xcfa.analysis.*
import hu.bme.mit.theta.xcfa.cli.params.*
import hu.bme.mit.theta.xcfa.cli.utils.getSolver
import hu.bme.mit.theta.xcfa.model.XCFA
import java.util.*
import java.util.function.Predicate

fun getAsgCegarChecker(
  xcfa: XCFA,
  mcm: MCM,
  config: XcfaConfig<*, *>,
  logger: Logger,
): SafetyChecker<
  ASG<XcfaState<PtrState<*>>, XcfaAction>,
  ASGTrace<XcfaState<PtrState<*>>, XcfaAction>,
  XcfaPrec<*>,
> {
  checkState(
    config.inputConfig.property == ErrorDetection.TERMINATION,
    "Lasso checker should be used for checking termination!",
  )

  val loopCegarConfig = config.backendConfig.specConfig as LoopCegarConfig
  val abstractionSolverFactory: SolverFactory =
    getSolver(
      loopCegarConfig.abstractorConfig.abstractionSolver,
      loopCegarConfig.abstractorConfig.validateAbstractionSolver,
    )
  val refinementSolverFactory: SolverFactory =
    getSolver(
      loopCegarConfig.refinerConfig.refinementSolver,
      loopCegarConfig.refinerConfig.validateRefinementSolver,
    )

  val ignoredVarRegistry = mutableMapOf<VarDecl<*>, MutableSet<ExprState>>()

  val lts = ConeOfInfluenceMode.NO_COI.getLts(xcfa, ignoredVarRegistry, POR.NOPOR)

  val abstractionSolverInstance = abstractionSolverFactory.createSolver()

  val statePredicate =
    if (loopCegarConfig.abstractorConfig.domain == Domain.EXPL) {
      Predicate { xcfaState: XcfaState<PtrState<ExplState>>? ->
        ExprStatePredicate(xcfa.initProcedures[0].first.prop, abstractionSolverInstance)
          .test(xcfaState!!.sGlobal.innerState)
      }
    } else {
      Predicate { xcfaState: XcfaState<PtrState<PredState>>? ->
        ExprStatePredicate(xcfa.initProcedures[0].first.prop, abstractionSolverInstance)
          .test(xcfaState!!.sGlobal.innerState)
      }
    }

  //  val statePredicate = if(loopCegarConfig.abstractorConfig.domain == Domain.EXPL) {
  //    Predicate { xcfaState: XcfaState<PtrState<ExplState>>? ->
  //      if (xcfaState!!.sGlobal.innerState.isBottom) {
  //        false
  //      } else {
  //        try {
  //          val valuation = xcfaState!!.sGlobal.innerState.`val`
  //          val prop =
  //            ExprUtils.changeDecls(
  //              xcfa.initProcedures[0].first.prop,
  //              xcfaState.processes.getOrDefault(0, null)?.varLookup?.getOrNull(0)
  //                ?: emptyMap<VarDecl<*>, VarDecl<*>>(),
  //            )
  //          prop.eval(valuation).equals(True())
  //        } catch (e: NoSuchElementException) {
  //          false
  //        }
  //      }
  //    }

  val abstractor =
    loopCegarConfig.abstractorConfig.domain.asgAbstractor(
      xcfa,
      abstractionSolverInstance,
      loopCegarConfig.abstractorConfig.maxEnum,
      logger,
      lts,
      loopCegarConfig.abstractorConfig.search,
      getPartialOrder(
        loopCegarConfig.abstractorConfig.domain.partialOrd(abstractionSolverInstance)
          as PartialOrd<PtrState<ExprState>>
      ),
      statePredicate as Predicate<XcfaState<PtrState<ExprState>>?>,
      null,
    )

  val asg = abstractor.createProof()

  val atomicNodePruner: NodePruner<ExprState, ExprAction> =
    loopCegarConfig.abstractorConfig.domain.nodePruner as NodePruner<ExprState, ExprAction>

  val precRefiner =
    loopCegarConfig.abstractorConfig.domain.itpPrecRefiner(
      loopCegarConfig.refinerConfig.exprSplitter.exprSplitter
    ) as PrecRefiner<ExprState, ExprAction, Prec, ItpRefutation>

  val refiner =
    SingleASGTraceRefiner(
      loopCegarConfig.refinerConfig.refinement,
      refinementSolverFactory,
      precRefiner,
      logger,
    )

  val checker =
    AsgCegarChecker.create(
      abstractor as ASGAbstractor<ExprState, ExprAction, Prec>,
      refiner,
      logger,
    )

  return object :
    SafetyChecker<
      ASG<XcfaState<PtrState<*>>, XcfaAction>,
      ASGTrace<XcfaState<PtrState<*>>, XcfaAction>,
      XcfaPrec<*>,
    > {
    override fun check(
      prec: XcfaPrec<*>?
    ): SafetyResult<
      ASG<XcfaState<PtrState<*>>, XcfaAction>,
      ASGTrace<XcfaState<PtrState<*>>, XcfaAction>,
    > {
      return checker.check(prec)
        as
        SafetyResult<
          ASG<XcfaState<PtrState<*>>, XcfaAction>,
          ASGTrace<XcfaState<PtrState<*>>, XcfaAction>,
        >
    }

    override fun check():
      SafetyResult<
        ASG<XcfaState<PtrState<*>>, XcfaAction>,
        ASGTrace<XcfaState<PtrState<*>>, XcfaAction>,
      > {
      return check(loopCegarConfig.abstractorConfig.domain.initPrec(xcfa, loopCegarConfig.initPrec))
    }
  }
}
