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
package hu.bme.mit.theta.analysis.algorithm.mdd.cegar

import hu.bme.mit.delta.java.mdd.JavaMddFactory
import hu.bme.mit.delta.java.mdd.MddHandle
import hu.bme.mit.delta.java.mdd.MddSignature
import hu.bme.mit.delta.java.mdd.MddVariableOrder
import hu.bme.mit.delta.mdd.MddInterpreter
import hu.bme.mit.delta.mdd.MddVariableDescriptor
import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.algorithm.bounded.ImplicitPredicateAbstractor
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr
import hu.bme.mit.theta.analysis.algorithm.bounded.action
import hu.bme.mit.theta.analysis.algorithm.bounded.orderVars
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.impl.AndNextStateDescriptor
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.impl.MddNodeNextStateDescriptor
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.impl.MddNodePostcondition
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.impl.OnTheFlyReachabilityNextStateDescriptor
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.impl.OrNextStateDescriptor
import hu.bme.mit.theta.analysis.algorithm.mdd.fixedpoint.IterationStrategy
import hu.bme.mit.theta.analysis.algorithm.mdd.fixedpoint.StateSpaceEnumerationProvider
import hu.bme.mit.theta.analysis.algorithm.mdd.node.expression.ExprLatticeDefinition
import hu.bme.mit.theta.analysis.algorithm.mdd.node.expression.MddExpressionRepresentation
import hu.bme.mit.theta.analysis.algorithm.mdd.node.expression.MddExpressionTemplate
import hu.bme.mit.theta.analysis.algorithm.mdd.result.MddAnalysisStatistics
import hu.bme.mit.theta.analysis.algorithm.mdd.result.MddProof
import hu.bme.mit.theta.analysis.algorithm.mdd.trace.TraceSearch
import hu.bme.mit.theta.analysis.algorithm.mdd.trace.generateTrace
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceChecker
import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation
import hu.bme.mit.theta.analysis.expr.refinement.JoiningPrecRefiner
import hu.bme.mit.theta.analysis.expr.refinement.PrecRefiner
import hu.bme.mit.theta.analysis.pred.ExprSplitters
import hu.bme.mit.theta.analysis.pred.ItpRefToPredPrec
import hu.bme.mit.theta.analysis.pred.PredPrec
import hu.bme.mit.theta.analysis.pred.PredState
import hu.bme.mit.theta.analysis.unit.UnitPrec
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.common.stopwatch.Stopwatch
import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Not
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.PathUtils
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory
import hu.bme.mit.theta.solver.SolverPool

/**
 * CEGAR over implicit predicate abstraction where each iteration's saturation is constrained to the
 * previous iteration's reachable set.
 */
class MddCegarChecker
@JvmOverloads
constructor(
  private val concreteModel: MonolithicExpr,
  private val solverPool: SolverPool,
  private val logger: Logger,
  private val traceCheckerFactory: (MonolithicExpr) -> ExprTraceChecker<ItpRefutation>,
  private val iterationStrategy: IterationStrategy = IterationStrategy.GSAT,
  private val initPrec: (MonolithicExpr) -> PredPrec = { model ->
    PredPrec.of(listOf(model.propExpr, model.initExpr))
  },
  private val precRefiner: PrecRefiner<PredState, ExprAction, PredPrec, ItpRefutation> =
    JoiningPrecRefiner.create(ItpRefToPredPrec(ExprSplitters.atoms())),
  private val useReachConstraint: Boolean = true,
  private val useOnTheFlyReachability: Boolean = false,
  private val traceTimeout: Long = 10,
  private val lookAheadStrategy: MddExpressionRepresentation.MddToExprStrategy =
    MddExpressionRepresentation.MddToExprStrategy.NONE,
  private val proofStrategy: MddExpressionRepresentation.MddToExprStrategy =
    MddExpressionRepresentation.MddToExprStrategy.NODE_LEVEL,
  private val traceSearch: TraceSearch = TraceSearch.DFS,
) : SafetyChecker<MddProof, Trace<ExplState, ExprAction>, UnitPrec> {

  init {
    require(!(useOnTheFlyReachability && useReachConstraint)) {
      "on-the-fly reachability cannot combine with the reach-set constraint: early termination " +
        "leaves the constraint unsound"
    }
  }

  override fun check(prec: UnitPrec?): SafetyResult<MddProof, Trace<ExplState, ExprAction>> {
    val totalTime = Stopwatch.createStarted()

    val orders = CegarOrders(concreteModel)
    orders.stateOrder.mddGraph.setAttribute(
      MddExpressionRepresentation.LOOK_AHEAD,
      lookAheadStrategy,
    )
    orders.transOrder.mddGraph.setAttribute(
      MddExpressionRepresentation.LOOK_AHEAD,
      lookAheadStrategy,
    )

    val abstractor = ImplicitPredicateAbstractor(concreteModel)
    val traceChecker = traceCheckerFactory(concreteModel)
    var currentPrec = initPrec(concreteModel)
    var prevStateSpace: MddHandle? = null

    // one provider for the whole run: its caches are keyed by (node, descriptor), so a refined
    // relation never gets a false hit while the unchanged concrete sub-structure is reused
    val provider = iterationStrategy.createProvider(orders.stateOrder)

    var totalSolverCalls = 0L
    var i = 0

    while (true) {
      i++
      val (model, newLits) = abstractor.abstractModel(currentPrec)

      newLits.forEach(orders::createLevelOnTop)

      val constraint = if (useReachConstraint) prevStateSpace else null

      val iter = runIteration(model, constraint, orders, provider)
      totalSolverCalls += iter.relationSolverCalls + iter.saturationSolverCalls

      logger.write(
        Logger.Level.MAINSTEP,
        "CEGAR iteration %d: |prec|=%d, newLiterals=%d, relationChecks=%d, saturationChecks=%d, " +
          "stateSpace=%d, violating=%d, cacheHit=%d/%d, ssgTime=%dms\n",
        i,
        currentPrec.preds.size,
        newLits.size,
        iter.relationSolverCalls,
        iter.saturationSolverCalls,
        iter.stateSpaceSize,
        iter.violatingSize,
        iter.hitCount,
        iter.queryCount,
        iter.ssgTimeMs,
      )

      if (iter.violatingSize == 0L) {
        totalTime.stop()
        logSummary(i, totalSolverCalls, totalTime.elapsedMillis())
        return SafetyResult.safe(
          MddProof.of(iter.stateSpace, proofStrategy),
          statisticsOf(iter, totalTime.elapsedMillis()),
        )
      }

      checkNotNull(iter.trace) {
        "CEGAR iteration $i found a violation but trace generation timed out"
      }

      val predTrace = abstractor.toPredTrace(iter.trace)
      val res = traceChecker.check(predTrace)
      if (res.isFeasible) {
        totalTime.stop()
        logSummary(i, totalSolverCalls, totalTime.elapsedMillis())
        val valuations = res.asFeasible().valuations
        val cex =
          Trace.of(
            valuations.states.map { ExplState.of(it) },
            valuations.actions.map { concreteModel.action() },
          )
        return SafetyResult.unsafe(
          cex,
          MddProof.of(iter.stateSpace, proofStrategy),
          statisticsOf(iter, totalTime.elapsedMillis()),
        )
      }

      val refutation = res.asInfeasible().refutation
      currentPrec = precRefiner.refine(currentPrec, predTrace, refutation)
      currentPrec =
        PredPrec.of(
          currentPrec.preds.filter { pred ->
            ExprUtils.getVars(pred).any { it !in concreteModel.ctrlVars }
          }
        )

      prevStateSpace = iter.stateSpace
    }
  }

  private data class IterationResult(
    val stateSpace: MddHandle,
    val violatingSize: Long,
    val stateSpaceSize: Long,
    val trace: Trace<ExplState, ExprAction>?,
    val relationSolverCalls: Long,
    val saturationSolverCalls: Long,
    val ssgTimeMs: Long,
    val hitCount: Long,
    val queryCount: Long,
    val cacheSize: Long,
  )

  private fun runIteration(
    model: MonolithicExpr,
    prevStateSpace: MddHandle?,
    orders: CegarOrders,
    provider: StateSpaceEnumerationProvider,
  ): IterationResult {
    val stateSig: MddSignature = orders.stateOrder.defaultSetSignature
    val transSig: MddSignature = orders.transOrder.defaultSetSignature

    // the abstract init and relation are non-empty whenever the concrete ones are (the literal
    // definitions are always satisfiable), so their root satisfiability check is skipped; the prop
    // node has no such guarantee
    val initNode = stateNode(PathUtils.unfold(model.initExpr, 0), stateSig, true)

    val relSolverBefore = solverPool.checkCount
    val transNodes =
      model.split.map { expr ->
        transSig.topVariableHandle.checkInNode(
          MddExpressionTemplate.ofKnownSat(
            PathUtils.unfold(expr, VarIndexingFactory.indexing(0)),
            { it as Decl<*> },
            solverPool,
            true,
          )
        )
      }
    val propNode = stateNode(PathUtils.unfold(Not(model.propExpr), 0), stateSig)
    val relSolverCalls = solverPool.checkCount - relSolverBefore

    val relation =
      OrNextStateDescriptor.create(transNodes.map { MddNodeNextStateDescriptor.of(it) })
    // the constraint is lifted under the current top, so the interpreter floats it over the literal
    // levels added since it was built
    val constrained =
      if (prevStateSpace == null) relation
      else
        AndNextStateDescriptor.of(
          MddNodePostcondition.of(stateSig.topVariableHandle.getHandleFor(prevStateSpace.node)),
          relation,
        )
    val nextStates =
      if (useOnTheFlyReachability) OnTheFlyReachabilityNextStateDescriptor.of(constrained, propNode)
      else constrained

    val satSolverBefore = solverPool.checkCount
    val ssgTime = Stopwatch.createStarted()
    val stateSpace =
      provider.compute(MddNodePostcondition.of(initNode), nextStates, stateSig.topVariableHandle)
    ssgTime.stop()
    val satSolverCalls = solverPool.checkCount - satSolverBefore

    val propViolating = stateSpace.intersection(propNode)
    val violatingSize = MddInterpreter.calculateNonzeroCount(propViolating)
    val stateSpaceSize = MddInterpreter.calculateNonzeroCount(stateSpace)

    val trace =
      if (violatingSize != 0L)
        generateTrace(
          transNodes,
          transSig,
          stateSpace,
          propViolating,
          initNode,
          stateSig,
          model,
          traceTimeout,
          logger,
          search = traceSearch,
        )
      else null

    return IterationResult(
      stateSpace,
      violatingSize,
      stateSpaceSize,
      trace,
      relSolverCalls,
      satSolverCalls,
      ssgTime.elapsedMillis(),
      provider.hitCount,
      provider.queryCount,
      provider.cacheSize,
    )
  }

  private fun stateNode(
    expr: Expr<BoolType>,
    sig: MddSignature,
    knownSat: Boolean = false,
  ): MddHandle =
    sig.topVariableHandle.checkInNode(
      if (knownSat) MddExpressionTemplate.ofKnownSat(expr, { it as Decl<*> }, solverPool, false)
      else MddExpressionTemplate.of(expr, { it as Decl<*> }, solverPool)
    )

  private fun statisticsOf(iter: IterationResult, totalTimeMs: Long) =
    MddAnalysisStatistics(
      iter.violatingSize,
      iter.stateSpaceSize,
      iter.hitCount,
      iter.queryCount,
      iter.cacheSize,
      iter.ssgTimeMs,
      totalTimeMs,
    )

  private fun logSummary(iterations: Int, totalSolverCalls: Long, totalTimeMs: Long) {
    logger.write(
      Logger.Level.MAINSTEP,
      "CEGAR finished: iterations=%d, totalSolverChecks=%d, totalTime=%dms, reachConstraint=%b\n",
      iterations,
      totalSolverCalls,
      totalTimeMs,
      useReachConstraint,
    )
  }
}

/**
 * The variable orders of one CEGAR run: the ctrl levels at the bottom, literal levels added on top
 * per refinement.
 */
private class CegarOrders(concreteModel: MonolithicExpr) {

  val stateOrder: MddVariableOrder =
    JavaMddFactory.getDefault()
      .createMddVariableOrder(
        JavaMddFactory.getDefault().createMddGraph(ExprLatticeDefinition.forExpr())
      )
  val transOrder: MddVariableOrder =
    JavaMddFactory.getDefault()
      .createMddVariableOrder(
        JavaMddFactory.getDefault().createMddGraph(ExprLatticeDefinition.forExpr())
      )

  init {
    // createOnTop builds bottom-up: reversed, so the first ctrl var ends up highest
    concreteModel
      .orderVars()
      .filter { it in concreteModel.ctrlVars }
      .reversed()
      .forEach(::createLevelOnTop)
  }

  /** Abstract vars (ctrl vars and literals) always have offset 1 in the abstract relation. */
  fun createLevelOnTop(v: VarDecl<*>) {
    stateOrder.createOnTop(MddVariableDescriptor.create(v.getConstDecl(0), 0))
    transOrder.createOnTop(MddVariableDescriptor.create(v.getConstDecl(1), 0))
    transOrder.createOnTop(MddVariableDescriptor.create(v.getConstDecl(0), 0))
  }
}
