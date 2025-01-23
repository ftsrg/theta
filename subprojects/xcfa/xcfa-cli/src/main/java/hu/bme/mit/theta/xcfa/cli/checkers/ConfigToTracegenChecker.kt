/*
 *  Copyright 2024-2025 Budapest University of Technology and Economics
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
import hu.bme.mit.theta.analysis.algorithm.Checker
import hu.bme.mit.theta.analysis.algorithm.Result
import hu.bme.mit.theta.analysis.algorithm.arg.ArgNode
import hu.bme.mit.theta.analysis.algorithm.cegar.BasicArgAbstractor
import hu.bme.mit.theta.analysis.algorithm.cegar.abstractor.StopCriterions
import hu.bme.mit.theta.analysis.algorithm.tracegeneration.TraceGenerationChecker
import hu.bme.mit.theta.analysis.algorithm.tracegeneration.summary.AbstractTraceSummary
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.refinement.*
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.analysis.waitlist.PriorityWaitlist
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.graphsolver.patterns.constraints.MCM
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.xcfa.analysis.*
import hu.bme.mit.theta.xcfa.cli.params.*
import hu.bme.mit.theta.xcfa.cli.utils.getSolver
import hu.bme.mit.theta.xcfa.model.XCFA

fun getTracegenChecker(
  xcfa: XCFA,
  mcm: MCM,
  config: XcfaConfig<*, *>,
  logger: Logger,
): Checker<AbstractTraceSummary<XcfaState<*>, XcfaAction>, XcfaPrec<*>> {
  val tracegenConfig = config.backendConfig.specConfig as TracegenConfig
  val ignoredVarRegistry = mutableMapOf<VarDecl<*>, MutableSet<ExprState>>()

  val lts = ConeOfInfluenceMode.NO_COI.getLts(xcfa, ignoredVarRegistry, POR.NOPOR)

  val abstractionSolverFactory: SolverFactory =
    getSolver(
      tracegenConfig.abstractorConfig.abstractionSolver,
      tracegenConfig.abstractorConfig.validateAbstractionSolver,
    )

  val waitlist =
    PriorityWaitlist.create<ArgNode<out XcfaState<PtrState<ExprState>>, XcfaAction>>(
      tracegenConfig.abstractorConfig.search.getComp(xcfa)
    )

  val abstractionSolverInstance = abstractionSolverFactory.createSolver()
  val globalStatePartialOrd: PartialOrd<PtrState<ExprState>> =
    tracegenConfig.abstractorConfig.domain.partialOrd(abstractionSolverInstance)
      as PartialOrd<PtrState<ExprState>>
  val corePartialOrd: PartialOrd<XcfaState<PtrState<ExprState>>> =
    if (xcfa.isInlined) getPartialOrder(globalStatePartialOrd)
    else getStackPartialOrder(globalStatePartialOrd)
  val abstractor: BasicArgAbstractor<ExprState, ExprAction, Prec> =
    tracegenConfig.abstractorConfig.domain.abstractor(
      xcfa,
      abstractionSolverInstance,
      tracegenConfig.abstractorConfig.maxEnum,
      waitlist,
      StopCriterions.fullExploration(),
      logger,
      lts,
      config.inputConfig.property,
      corePartialOrd,
      tracegenConfig.abstractorConfig.havocMemory,
    ) as BasicArgAbstractor<ExprState, ExprAction, Prec>

  val tracegenChecker = TraceGenerationChecker.create(logger, abstractor, false)

  return Checker<AbstractTraceSummary<XcfaState<*>, XcfaAction>, XcfaPrec<*>> { prec ->
    tracegenChecker.check(prec) as Result<AbstractTraceSummary<XcfaState<*>, XcfaAction>>
  }
}
