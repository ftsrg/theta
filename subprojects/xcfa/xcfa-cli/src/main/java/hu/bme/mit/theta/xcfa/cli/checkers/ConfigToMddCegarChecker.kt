/*
 *  Copyright 2026 Budapest University of Technology and Economics
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

import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.MonolithicExprPass
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.passes.L2SMEPass
import hu.bme.mit.theta.analysis.algorithm.mdd.cegar.MddCegarChecker
import hu.bme.mit.theta.analysis.algorithm.mdd.result.MddProof
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expr.refinement.JoiningPrecRefiner
import hu.bme.mit.theta.analysis.expr.refinement.createBwBinItpCheckerFactory
import hu.bme.mit.theta.analysis.expr.refinement.createFwBinItpCheckerFactory
import hu.bme.mit.theta.analysis.expr.refinement.createSeqItpCheckerFactory
import hu.bme.mit.theta.analysis.pred.ItpRefToPredPrec
import hu.bme.mit.theta.xcfa.cli.params.MddCegarRefinement
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.analysis.unit.UnitPrec
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.cbool.CBool
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.solver.SolverPool
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.analysis.monolithic.XcfaPipelineChecker
import hu.bme.mit.theta.xcfa.analysis.proof.LocationInvariants
import hu.bme.mit.theta.xcfa.cli.params.MddCegarConfig
import hu.bme.mit.theta.xcfa.cli.params.XcfaConfig
import hu.bme.mit.theta.xcfa.cli.utils.getSolver
import hu.bme.mit.theta.xcfa.model.XCFA

fun getMddCegarChecker(
  xcfa: XCFA,
  parseContext: ParseContext,
  config: XcfaConfig<*, *>,
  logger: Logger,
): SafetyChecker<LocationInvariants, Trace<XcfaState<PtrState<ExplState>>, XcfaAction>, UnitPrec> {
  val mddCegarConfig = config.backendConfig.specConfig as MddCegarConfig

  val solverFactory: SolverFactory = getSolver(mddCegarConfig.solver, mddCegarConfig.validateSolver)

  val solverPool = SolverPool(solverFactory)

  val refinementSolverFactory: SolverFactory =
    if (mddCegarConfig.refinementSolver.isEmpty() || mddCegarConfig.refinementSolver == mddCegarConfig.solver)
      solverFactory
    else getSolver(mddCegarConfig.refinementSolver, mddCegarConfig.validateSolver)
  val traceCheckerFactory =
    when (mddCegarConfig.refinement) {
      MddCegarRefinement.SEQ_ITP -> createSeqItpCheckerFactory(refinementSolverFactory)
      MddCegarRefinement.FW_BIN_ITP -> createFwBinItpCheckerFactory(refinementSolverFactory)
      MddCegarRefinement.BW_BIN_ITP -> createBwBinItpCheckerFactory(refinementSolverFactory)
    }

  // Boolean variables assigned at most once per transition are tracked explicitly, like the control
  // variables, instead of through predicates: their two values cost the MDD nothing and every
  // predicate over them would only carve the same two cells.
  fun isBoolean(v: VarDecl<*>): Boolean {
    if (v.type is BoolType) return true
    // C's _Bool is an integer type in the frontend; the metadata still knows it
    return try {
      CComplexType.getType(v.ref, parseContext) is CBool
    } catch (e: Exception) {
      false
    }
  }

  fun promoteBools(me: MonolithicExpr): MonolithicExpr {
    if (!mddCegarConfig.explicitBools) return me
    val promoted =
      me.vars.filter { it !in me.ctrlVars && me.transOffsetIndex[it] >= 1 && isBoolean(it) }
    if (promoted.isEmpty()) return me
    logger.write(Logger.Level.MAINSTEP, "Explicit Boolean variables: %d\n", promoted.size)
    return me.copy(ctrlVars = me.ctrlVars + promoted)
  }

  val baseChecker = { rawExpr: MonolithicExpr ->
    val monolithicExpr = promoteBools(rawExpr)
    MddCegarChecker(
      monolithicExpr,
      solverPool,
      logger,
      traceCheckerFactory,
      iterationStrategy = mddCegarConfig.iterationStrategy,
      useReachConstraint = mddCegarConfig.reachConstraint,
      useOnTheFlyReachability = mddCegarConfig.onTheFlyReachability,
      traceTimeout = mddCegarConfig.traceTimeout,
      useTransitionSeeding = mddCegarConfig.transitionSeeding,
      useTransitionBound = mddCegarConfig.transitionBound,
      lookAheadStrategy = mddCegarConfig.lookAheadStrategy,
      proofStrategy = mddCegarConfig.proofStrategy,
      splitRelation = mddCegarConfig.splitRelation,
      perStepRefinement = mddCegarConfig.perStepRefinement,
      precRefiner =
        JoiningPrecRefiner.create(ItpRefToPredPrec(mddCegarConfig.predSplit.exprSplitter)),
      literalPlacement = mddCegarConfig.literalPlacement,
      tracesPerIteration = mddCegarConfig.tracesPerIteration,
      clearCaches = mddCegarConfig.clearCaches,
      adaptivePredSplit = mddCegarConfig.adaptivePredSplit,
      forceEvents = mddCegarConfig.forceEvents,
      forceReverse = mddCegarConfig.forceReverse,
      traceSearch = mddCegarConfig.traceSearch,
    )
  }
  val passes = mutableListOf<MonolithicExprPass<MddProof>>()

  if (config.inputConfig.property.verifiedProperty == ErrorDetection.TERMINATION) {
    passes.add(L2SMEPass())
  }

  return XcfaPipelineChecker(
    xcfa,
    config.inputConfig.property,
    parseContext,
    baseChecker,
    passes,
    logger,
    config.outputConfig.acceptUnreliableSafe,
    true,
  )
}
