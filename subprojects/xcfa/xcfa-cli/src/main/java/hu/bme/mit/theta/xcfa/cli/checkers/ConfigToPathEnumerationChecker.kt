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

import hu.bme.mit.theta.analysis.Analysis
import hu.bme.mit.theta.analysis.PartialOrd
import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.EmptyProof
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker
import hu.bme.mit.theta.analysis.algorithm.bounded.BoundedLtsChecker
import hu.bme.mit.theta.analysis.algorithm.cegar.ArgAbstractor
import hu.bme.mit.theta.analysis.algorithm.cegar.abstractor.StopCriterions
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.ptr.PtrPrec
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.analysis.waitlist.PriorityWaitlist
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.xcfa.analysis.*
import hu.bme.mit.theta.xcfa.cli.params.PathEnumerationConfig
import hu.bme.mit.theta.xcfa.cli.params.XcfaConfig
import hu.bme.mit.theta.xcfa.cli.utils.getSolver
import hu.bme.mit.theta.xcfa.dereferences
import hu.bme.mit.theta.xcfa.model.XCFA

fun getPathEnumerationChecker(
  xcfa: XCFA,
  config: XcfaConfig<*, *>,
  logger: Logger,
): SafetyChecker<
  EmptyProof,
  Trace<XcfaState<PtrState<ExprState>>, XcfaAction>,
  XcfaPrec<PtrPrec<Prec>>,
> {
  val pathEnumerationConfig = config.backendConfig.specConfig as PathEnumerationConfig
  if (
    config.inputConfig.property == ErrorDetection.DATA_RACE &&
      xcfa.procedures.any { it.edges.any { it.label.dereferences.isNotEmpty() } }
  ) {
    throw RuntimeException("DATA_RACE cannot be checked when pointers exist in the file.")
  }
  if (pathEnumerationConfig.porLevel.isDynamic) {
    throw RuntimeException("Path enumeration does not support DPOR.")
  }
  if (pathEnumerationConfig.porLevel.isAbstractionAware) {
    throw RuntimeException("Path enumeration does not support AAPOR.")
  }
  val pathEnumerationSolverFactory: SolverFactory =
    getSolver(
      pathEnumerationConfig.pathEnumerationSolver,
      pathEnumerationConfig.validatePathEnumerationSolver,
    )
  val abstractionSolverFactory: SolverFactory =
    getSolver(
      pathEnumerationConfig.abstractionSolver,
      pathEnumerationConfig.validateAbstractionSolver,
    )

  val ignoredVarRegistry = mutableMapOf<VarDecl<*>, MutableSet<ExprState>>()
  val lts =
    pathEnumerationConfig.coi.getLts(xcfa, ignoredVarRegistry, pathEnumerationConfig.porLevel)

  val abstractionSolverInstance = abstractionSolverFactory.createSolver()
  val globalStatePartialOrd =
    pathEnumerationConfig.domain.partialOrd(abstractionSolverInstance)
      as PartialOrd<PtrState<ExprState>>
  val corePartialOrd: PartialOrd<XcfaState<PtrState<ExprState>>> =
    if (xcfa.isInlined) getPartialOrder(globalStatePartialOrd)
    else getStackPartialOrder(globalStatePartialOrd)
  val abstractor =
    pathEnumerationConfig.domain.abstractor(
      xcfa,
      abstractionSolverInstance,
      pathEnumerationConfig.maxEnum,
      PriorityWaitlist.create(),
      StopCriterions.fullExploration(),
      logger,
      lts,
      config.inputConfig.property,
      corePartialOrd,
      pathEnumerationConfig.havocMemory,
    ) as ArgAbstractor<XcfaState<PtrState<ExprState>>, XcfaAction, XcfaPrec<PtrPrec<Prec>>>
  val argBuilder = abstractor.argBuilder
  val analysis =
    argBuilder.analysis
      as Analysis<XcfaState<PtrState<ExprState>>, XcfaAction, XcfaPrec<PtrPrec<Prec>>>
  val target = argBuilder.target
  val prec =
    pathEnumerationConfig.domain.initPrec(xcfa, pathEnumerationConfig.initPrec)
      as XcfaPrec<PtrPrec<Prec>>

  val pathEnumerationSolverInstance = pathEnumerationSolverFactory.createSolver()
  return BoundedLtsChecker(
    lts,
    analysis,
    target,
    pathEnumerationConfig.maxBound,
    prec,
    pathEnumerationSolverInstance,
  )
}
