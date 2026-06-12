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
package hu.bme.mit.theta.analysis.algorithm.mdd

import hu.bme.mit.delta.java.mdd.JavaMddFactory
import hu.bme.mit.delta.java.mdd.MddHandle
import hu.bme.mit.delta.java.mdd.MddSignature
import hu.bme.mit.delta.java.mdd.MddVariableHandle
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
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.AbstractNextStateDescriptor
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.impl.ConstraintDrivenAndNextStateDescriptor
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.impl.MddNodeInitializer
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.impl.MddNodeNextStateDescriptor
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.impl.OnTheFlyReachabilityNextStateDescriptor
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.impl.OrNextStateDescriptor
import hu.bme.mit.theta.analysis.algorithm.mdd.expressionnode.ExprLatticeDefinition
import hu.bme.mit.theta.analysis.algorithm.mdd.expressionnode.MddExpressionRepresentation
import hu.bme.mit.theta.analysis.algorithm.mdd.expressionnode.MddExpressionTemplate
import hu.bme.mit.theta.analysis.algorithm.mdd.fixedpoint.IterationStrategy
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
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Not
import hu.bme.mit.theta.core.utils.PathUtils
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory
import hu.bme.mit.theta.solver.SolverPool

/**
 * Builds the relation nodes of an abstract model's transition relation. The default implementation
 * is the `MddExpressionTemplate` path used by `MddChecker`; a store-backed builder that reuses
 * concrete transitions discovered in earlier iterations (CEGAR phase 2) plugs in here.
 */
fun interface TransitionNodeBuilder {

  fun build(
    model: MonolithicExpr,
    transTop: MddVariableHandle,
    identityExprs: List<Expr<BoolType>>,
    solverPool: SolverPool,
  ): List<MddHandle>

  companion object {

    val DEFAULT = TransitionNodeBuilder { model, transTop, identityExprs, solverPool ->
      model.split.map { expr ->
        val transExpr =
          And(PathUtils.unfold(expr, VarIndexingFactory.indexing(0)), And(identityExprs))
        transTop.checkInNode(
          MddExpressionTemplate.of(transExpr, { it as Decl<*> }, solverPool, true)
        )
      }
    }
  }
}

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
    JoiningPrecRefiner.create(ItpRefToPredPrec(ExprSplitters.whole())),
  private val useReachConstraint: Boolean = true,
  private val useOnTheFlyReachability: Boolean = false,
  private val traceTimeout: Long = 10,
  private val transitionNodeBuilder: TransitionNodeBuilder = TransitionNodeBuilder.DEFAULT,
  private val useTransitionSeeding: Boolean = false,
  private val lookAheadStrategy: MddExpressionRepresentation.MddToExprStrategy =
    MddExpressionRepresentation.MddToExprStrategy.NONE,
  private val proofStrategy: MddExpressionRepresentation.MddToExprStrategy =
    MddExpressionRepresentation.MddToExprStrategy.NODE_LEVEL,
) : SafetyChecker<MddProof, Trace<ExplState, ExprAction>, UnitPrec> {

  init {
    require(!(useReachConstraint && useOnTheFlyReachability)) {
      "useReachConstraint and useOnTheFlyReachability cannot both be enabled: combining them is not sound"
    }
  }

  override fun check(prec: UnitPrec?): SafetyResult<MddProof, Trace<ExplState, ExprAction>> {
    val totalTime = Stopwatch.createStarted()
    MddExpressionRepresentation.setLookAheadStrategy(lookAheadStrategy)

    val stateGraph = JavaMddFactory.getDefault().createMddGraph(ExprLatticeDefinition.forExpr())
    val transGraph = JavaMddFactory.getDefault().createMddGraph(ExprLatticeDefinition.forExpr())
    val stateOrder = JavaMddFactory.getDefault().createMddVariableOrder(stateGraph)
    val transOrder = JavaMddFactory.getDefault().createMddVariableOrder(transGraph)
    val identityExprs = mutableListOf<Expr<BoolType>>()

    val abstractor = ImplicitPredicateAbstractor(concreteModel)
    val traceChecker = traceCheckerFactory(concreteModel)
    var currentPrec = initPrec(concreteModel)
    var reachExplicit: MddHandle? = null
    var prevTransNodes: List<MddHandle> = emptyList()
    // ctrl vars sit at the bottom, in the concrete model's relative ordering
    val orderedVars = concreteModel.orderVars()
    val ctrlOrdered = orderedVars.filter { it in concreteModel.ctrlVars }
    val dataOrdered = orderedVars.filter { it !in concreteModel.ctrlVars }

    if (useTransitionSeeding) {
      // concrete witness levels sit below all abstract levels; only the trans order gets them
      dataOrdered.reversed().forEach {
        createTransLevelOnTop(it, concreteModel.transOffsetIndex[it], transOrder, identityExprs)
      }
    }
    // createOnTop builds bottom-up, so reverse to keep ctrlOrdered[0] highest within the block
    ctrlOrdered.reversed().forEach { createLevelOnTop(it, stateOrder, transOrder, identityExprs) }

    var totalSolverCalls = 0L
    var i = 0

    while (true) {
      i++
      val (model, newLits) = abstractor.abstractModel(currentPrec)

      newLits.forEach { createLevelOnTop(it, stateOrder, transOrder, identityExprs) }

      val constraint =
        if (useReachConstraint && reachExplicit != null)
          stateOrder.defaultSetSignature.topVariableHandle.getHandleFor(reachExplicit.node)
        else null

      val iter =
        runIteration(
          model,
          constraint,
          stateOrder,
          transOrder,
          identityExprs,
          newLits,
          abstractor.literalToPred,
          prevTransNodes,
        )
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

      reachExplicit = iter.stateSpace
      if (useTransitionSeeding) prevTransNodes = iter.transNodes
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
    val transNodes: List<MddHandle>,
  )

  private fun runIteration(
    model: MonolithicExpr,
    constraint: MddHandle?,
    stateOrder: MddVariableOrder,
    transOrder: MddVariableOrder,
    identityExprs: List<Expr<BoolType>>,
    newLits: List<VarDecl<BoolType>>,
    literalToPred: Map<Decl<*>, Expr<BoolType>>,
    prevTransNodes: List<MddHandle>,
  ): IterationResult {
    val stateSig: MddSignature = stateOrder.defaultSetSignature
    val transSig: MddSignature = transOrder.defaultSetSignature

    val initExpr = PathUtils.unfold(model.initExpr, 0)
    val initNode =
      stateSig.topVariableHandle.checkInNode(
        MddExpressionTemplate.of(initExpr, { it as Decl<*> }, solverPool)
      )

    val relSolverBefore = solverPool.checkCount
    val transNodes =
      transitionNodeBuilder.build(model, transSig.topVariableHandle, identityExprs, solverPool)
    seedTransitions(prevTransNodes, transNodes, newLits, literalToPred, concreteModel, logger)
    val descriptors = transNodes.map { MddNodeNextStateDescriptor.of(it) }
    val nextStates: AbstractNextStateDescriptor = OrNextStateDescriptor.create(descriptors)

    val negatedPropExpr = PathUtils.unfold(Not(model.propExpr), 0)
    val propNode =
      stateSig.topVariableHandle.checkInNode(
        MddExpressionTemplate.of(negatedPropExpr, { it as Decl<*> }, solverPool)
      )
    val relSolverCalls = solverPool.checkCount - relSolverBefore

    val effectiveNextStates =
      if (constraint != null) ConstraintDrivenAndNextStateDescriptor.of(nextStates, constraint)
      else if (useOnTheFlyReachability)
        OnTheFlyReachabilityNextStateDescriptor.of(nextStates, propNode)
      else nextStates

    val satSolverBefore = solverPool.checkCount
    val ssgTime = Stopwatch.createStarted()
    val provider = iterationStrategy.createProvider(stateSig.variableOrder)
    val stateSpace =
      provider.compute(
        MddNodeInitializer.of(initNode),
        effectiveNextStates,
        stateSig.topVariableHandle,
      )
    ssgTime.stop()
    val satSolverCalls = solverPool.checkCount - satSolverBefore

    val propViolating = stateSpace.intersection(propNode) as MddHandle
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
      transNodes,
    )
  }

  /**
   * v1 insertion policy: top-insertion. This is the single seam where a reordering / mid-order
   * placement policy would plug in (guide decision 3). A non-top policy must also rebuild the
   * constraint for the new order, because the skip-level handle then stops being a pure
   * default-edge lift. Phase 2's bottom-sub-MDD sharing also assumes this literals-on-top
   * placement; other placements only degrade reuse, never correctness.
   */
  private fun createLevelOnTop(
    v: VarDecl<*>,
    stateOrder: MddVariableOrder,
    transOrder: MddVariableOrder,
    identityExprs: MutableList<Expr<BoolType>>,
  ) {
    stateOrder.createOnTop(MddVariableDescriptor.create(v.getConstDecl(0), 0))
    // abstract vars (ctrl vars and literals) always have offset 1 in the abstract relation
    createTransLevelOnTop(v, 1, transOrder, identityExprs)
  }

  private fun createTransLevelOnTop(
    v: VarDecl<*>,
    targetIndex: Int,
    transOrder: MddVariableOrder,
    identityExprs: MutableList<Expr<BoolType>>,
  ) {
    val domainSize = 0
    if (targetIndex > 0) {
      transOrder.createOnTop(MddVariableDescriptor.create(v.getConstDecl(targetIndex), domainSize))
    } else {
      transOrder.createOnTop(MddVariableDescriptor.create(v.getConstDecl(1), domainSize))
      identityExprs.add(Eq(v.getConstDecl(0).ref, v.getConstDecl(1).ref))
    }
    transOrder.createOnTop(MddVariableDescriptor.create(v.getConstDecl(0), domainSize))
  }

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
      "CEGAR finished: iterations=%d, totalSolverChecks=%d, totalTime=%dms, useReachConstraint=%b\n",
      iterations,
      totalSolverCalls,
      totalTimeMs,
      useReachConstraint,
    )
  }
}
