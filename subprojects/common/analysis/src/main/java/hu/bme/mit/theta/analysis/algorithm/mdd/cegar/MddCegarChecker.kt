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
import hu.bme.mit.theta.analysis.algorithm.bounded.orderVars
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
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Not
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.PathUtils
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory
import hu.bme.mit.theta.solver.SolverPool

/** CEGAR over implicit predicate abstraction, with saturation as the abstract model checker. */
class MddCegarChecker
@JvmOverloads
constructor(
  private val concreteModel: MonolithicExpr,
  private val solverPool: SolverPool,
  private val logger: Logger,
  private val traceCheckerFactory: (MonolithicExpr) -> ExprTraceChecker<ItpRefutation>,
  private val iterationStrategy: IterationStrategy = IterationStrategy.GSAT,
  // the property alone; an init predicate would connect every literal to every transition
  private val initPrec: (MonolithicExpr) -> PredPrec = { model ->
    PredPrec.of(listOf(model.propExpr))
  },
  private val precRefiner: PrecRefiner<PredState, ExprAction, PredPrec, ItpRefutation> =
    JoiningPrecRefiner.create(ItpRefToPredPrec(ExprSplitters.atoms())),
  private val useOnTheFlyReachability: Boolean = false,
  private val traceTimeout: Long = 10,
  private val lookAheadStrategy: MddExpressionRepresentation.MddToExprStrategy =
    MddExpressionRepresentation.MddToExprStrategy.NONE,
  private val proofStrategy: MddExpressionRepresentation.MddToExprStrategy =
    MddExpressionRepresentation.MddToExprStrategy.NODE_LEVEL,
  private val literalPlacement: LiteralPlacement = LiteralPlacement.FORCE,
  private val traceSearch: TraceSearch = TraceSearch.DFS,
) : SafetyChecker<MddProof, Trace<ExplState, ExprAction>, UnitPrec> {

  override fun check(prec: UnitPrec?): SafetyResult<MddProof, Trace<ExplState, ExprAction>> {
    val totalTime = Stopwatch.createStarted()

    var orders: CegarOrders? =
      if (literalPlacement == LiteralPlacement.FORCE) null else newOrders(null)

    val abstractor = ImplicitPredicateAbstractor(concreteModel)
    val traceChecker = traceCheckerFactory(concreteModel)
    var currentPrec = initPrec(concreteModel)

    // one provider for the run: its caches are keyed by (node, descriptor)
    var provider: StateSpaceEnumerationProvider? =
      orders?.let { iterationStrategy.createProvider(it.stateOrder) }

    var totalSolverCalls = 0L
    var i = 0

    while (true) {
      i++
      val abstraction = abstractor.abstractModel(currentPrec)
      val model = abstraction.model
      val newLits = abstraction.newLiterals

      val orderTime = Stopwatch.createStarted()
      if (literalPlacement == LiteralPlacement.FORCE) {
        val o = newOrders(model.orderVars())
        orders = o
        provider = iterationStrategy.createProvider(o.stateOrder)
      } else {
        newLits.forEach { orders!!.createLiteralLevel(it) }
      }
      orderTime.stop()
      val currentOrders = orders!!
      val currentProvider = provider!!

      val iter = runIteration(model, currentOrders, currentProvider)
      totalSolverCalls += iter.relationSolverCalls + iter.saturationSolverCalls

      logger.write(
        Logger.Level.MAINSTEP,
        "CEGAR iteration %d: |prec|=%d, newLiterals=%d, transitions=%d, relationChecks=%d, " +
          "saturationChecks=%d, stateSpace=%d, violating=%d, cacheHit=%d/%d, ssgTime=%dms, " +
          "orderTime=%dms\n",
        i,
        currentPrec.preds.size,
        newLits.size,
        model.split.size,
        iter.relationSolverCalls,
        iter.saturationSolverCalls,
        iter.stateSpaceSize,
        iter.violatingSize,
        iter.hitCount,
        iter.queryCount,
        iter.ssgTimeMs,
        orderTime.elapsedMillis(),
      )

      if (iter.violatingSize == 0L) {
        totalTime.stop()
        logSummary(i, totalSolverCalls, totalTime.elapsedMillis())
        return SafetyResult.safe(
          MddProof.of(iter.stateSpace, proofStrategy),
          statisticsOf(iter, totalTime.elapsedMillis()),
        )
      }

      val trace =
        checkNotNull(iter.trace) {
          "CEGAR iteration $i found a violation but trace generation timed out"
        }

      val refinementTime = Stopwatch.createStarted()
      val predTrace = abstractor.toPredTrace(trace)
      val res = traceChecker.check(predTrace)
      if (res.isFeasible) {
        totalTime.stop()
        logSummary(i, totalSolverCalls, totalTime.elapsedMillis())
        val valuations = res.asFeasible().valuations
        val cex =
          Trace.of<ExplState, ExprAction>(
            valuations.states.map { ExplState.of(it) },
            valuations.actions.map { it as ExprAction },
          )
        return SafetyResult.unsafe(
          cex,
          MddProof.of(iter.stateSpace, proofStrategy),
          statisticsOf(iter, totalTime.elapsedMillis()),
        )
      }
      val refined = precRefiner.refine(currentPrec, predTrace, res.asInfeasible().refutation)
      refinementTime.stop()
      val newPrec = PredPrec.of(dataPreds(refined))
      logger.write(
        Logger.Level.MAINSTEP,
        "CEGAR refinement %d: traceStates=%d, checkTime=%dms, newPreds=%d\n",
        i,
        trace.states.size,
        refinementTime.elapsedMillis(),
        newPrec.preds.size - currentPrec.preds.size,
      )
      currentPrec = newPrec
    }
  }

  private fun newOrders(fullOrder: List<VarDecl<*>>?): CegarOrders {
    val orders = CegarOrders(concreteModel, fullOrder)
    listOf(orders.stateOrder, orders.transOrder).forEach {
      it.mddGraph.setAttribute(MddExpressionRepresentation.LOOK_AHEAD, lookAheadStrategy)
    }
    return orders
  }

  private fun dataPreds(prec: PredPrec): List<Expr<BoolType>> =
    prec.preds.filter { p -> ExprUtils.getVars(p).any { it !in concreteModel.ctrlVars } }

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
    orders: CegarOrders,
    provider: StateSpaceEnumerationProvider,
  ): IterationResult {
    val stateSig: MddSignature = orders.stateOrder.defaultSetSignature
    val transSig: MddSignature = orders.transOrder.defaultSetSignature

    // the abstract init and relation are satisfiable whenever the concrete ones are
    val initNode = stateNode(PathUtils.unfold(model.initExpr, 0), stateSig, true)

    val relSolverBefore = solverPool.checkCount
    val transNodes =
      model.split.map { expr ->
        val transExpr =
          And(PathUtils.unfold(expr, VarIndexingFactory.indexing(0)), And(orders.identityExprs))
        transSig.topVariableHandle.checkInNode(
          MddExpressionTemplate.ofKnownSat(transExpr, { it as Decl<*> }, solverPool, true)
        )
      }
    val propNode = stateNode(PathUtils.unfold(Not(model.propExpr), 0), stateSig)
    val relSolverCalls = solverPool.checkCount - relSolverBefore

    val relation =
      OrNextStateDescriptor.create(transNodes.map { MddNodeNextStateDescriptor.of(it) })
    val nextStates =
      if (useOnTheFlyReachability) OnTheFlyReachabilityNextStateDescriptor.of(relation, propNode)
      else relation

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
      if (violatingSize == 0L) null
      else
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
          traceSearch,
        )

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
      "CEGAR finished: iterations=%d, totalSolverChecks=%d, totalTime=%dms\n",
      iterations,
      totalSolverCalls,
      totalTimeMs,
    )
  }
}

/** Where the literal levels go in the MDD orders. */
enum class LiteralPlacement {
  TOP,
  FORCE,
}

private class CegarOrders(concreteModel: MonolithicExpr, fullOrder: List<VarDecl<*>>? = null) {
  private val ctrlOffsets: Map<VarDecl<*>, Int> =
    concreteModel.ctrlVars.associateWith { concreteModel.transOffsetIndex[it] }

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
  val identityExprs = mutableListOf<Expr<BoolType>>()

  init {
    if (fullOrder != null) {
      fullOrder.reversed().forEach {
        if (it in concreteModel.ctrlVars) createLevelOnTop(it) else createLiteralLevel(it)
      }
    } else {
      concreteModel
        .orderVars()
        .filter { it in concreteModel.ctrlVars }
        .reversed()
        .forEach(::createLevelOnTop)
    }
  }

  fun createLevelOnTop(v: VarDecl<*>) {
    stateOrder.createOnTop(MddVariableDescriptor.create(v.getConstDecl(0), 0))
    createTransLevelOnTop(v, ctrlOffsets[v] ?: 1)
  }

  fun createLiteralLevel(v: VarDecl<*>) {
    val desc0 = MddVariableDescriptor.create(v.getConstDecl(0), 0)
    val desc1 = MddVariableDescriptor.create(v.getConstDecl(1), 0)
    stateOrder.createOnTop(desc0)
    transOrder.createOnTop(desc1)
    transOrder.createOnTop(desc0)
  }

  private fun createTransLevelOnTop(v: VarDecl<*>, targetIndex: Int) {
    if (targetIndex > 0) {
      transOrder.createOnTop(MddVariableDescriptor.create(v.getConstDecl(targetIndex), 0))
    } else {
      transOrder.createOnTop(MddVariableDescriptor.create(v.getConstDecl(1), 0))
      identityExprs.add(Eq(v.getConstDecl(0).ref, v.getConstDecl(1).ref))
    }
    transOrder.createOnTop(MddVariableDescriptor.create(v.getConstDecl(0), 0))
  }
}
