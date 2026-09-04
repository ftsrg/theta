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
import hu.bme.mit.delta.java.mdd.MddVariable
import hu.bme.mit.delta.java.mdd.MddVariableOrder
import hu.bme.mit.delta.mdd.MddInterpreter
import hu.bme.mit.delta.mdd.MddVariableDescriptor
import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.algorithm.bounded.ImplicitPredicateAbstractor
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr
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
import hu.bme.mit.theta.analysis.algorithm.mdd.trace.GeneratedTrace
import hu.bme.mit.theta.analysis.algorithm.mdd.trace.TraceSearch
import hu.bme.mit.theta.analysis.algorithm.mdd.trace.generateTrace
import hu.bme.mit.theta.analysis.algorithm.mdd.varordering.orderVarsFromRandomStartingPoints
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
  // the property only: a predicate over the init expression mentions every variable and would
  // connect every literal to every transition
  private val initPrec: (MonolithicExpr) -> PredPrec = { model ->
    PredPrec.of(listOf(model.propExpr))
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
  /**
   * Build the abstract relation per group of concrete transitions with the same connected literals.
   */
  private val splitRelation: Boolean = true,
  /**
   * Check the counterexample with the transition fired at each step instead of the whole relation.
   */
  private val perStepRefinement: Boolean = true,
  private val literalPlacement: LiteralPlacement = LiteralPlacement.TOP,
  /** Counterexamples (ending in distinct violating states) refined per iteration. */
  private val tracesPerIteration: Int = 1,
  /** Drop the saturation and SAT caches before every iteration. */
  private val clearCaches: Boolean = false,
  /** Refine with whole interpolants first, with [precRefiner] only when that adds nothing. */
  private val adaptivePredSplit: Boolean = false,
  private val forceEvents: ForceEvents = ForceEvents.DIRECT,
  private val forceReverse: Boolean = false,
  private val traceSearch: TraceSearch = TraceSearch.DFS,
) : SafetyChecker<MddProof, Trace<ExplState, ExprAction>, UnitPrec> {

  private val wholeRefiner: PrecRefiner<PredState, ExprAction, PredPrec, ItpRefutation> =
    JoiningPrecRefiner.create(ItpRefToPredPrec(ExprSplitters.whole()))

  // FORCE placement rebuilds the orders every iteration, so the previous reach set, a node of the
  // old orders, cannot be carried over
  private val applyReachConstraint =
    useReachConstraint && literalPlacement != LiteralPlacement.FORCE

  init {
    require(!(useOnTheFlyReachability && useReachConstraint)) {
      "on-the-fly reachability cannot combine with the reach-set constraint: early termination " +
        "leaves the constraint unsound"
    }
  }

  override fun check(prec: UnitPrec?): SafetyResult<MddProof, Trace<ExplState, ExprAction>> {
    val totalTime = Stopwatch.createStarted()

    // FORCE placement creates its orders per iteration, once the abstract model is known
    var orders: CegarOrders? =
      if (literalPlacement == LiteralPlacement.FORCE) null else newOrders(null)

    val abstractor = ImplicitPredicateAbstractor(concreteModel, splitRelation, perStepRefinement)
    val traceChecker = traceCheckerFactory(concreteModel)
    var currentPrec = initPrec(concreteModel)
    var prevStateSpace: MddHandle? = null

    // one provider for the run: its caches are keyed by (node, descriptor)
    var provider: StateSpaceEnumerationProvider? =
      orders?.let { iterationStrategy.createProvider(it.stateOrder) }

    var totalSolverCalls = 0L
    var i = 0
    // a fragment that adds no predicate switches the run to complete counterexamples
    var fragmentsAllowed = true

    while (true) {
      i++
      if (clearCaches && i > 1 && orders != null) {
        provider!!.clear()
        listOf(orders.stateOrder, orders.transOrder).forEach {
          it.mddGraph.getAttribute(MddExpressionTemplate.SAT_CACHE)?.clear()
        }
      }
      val abstraction = abstractor.abstractModel(currentPrec)
      val model = abstraction.model
      val newLits = abstraction.newLiterals

      val orderTime = Stopwatch.createStarted()
      if (literalPlacement == LiteralPlacement.FORCE) {
        // the levels of an existing order cannot be permuted: orders, graphs and caches are rebuilt
        val ordered =
          when (forceEvents) {
            ForceEvents.DIRECT -> model.orderVars()
            ForceEvents.CLOSURE ->
              orderVarsFromRandomStartingPoints(model.vars, abstraction.closureEvents, 50)
          }
        val o = newOrders(if (forceReverse) ordered.reversed() else ordered)
        orders = o
        provider = iterationStrategy.createProvider(o.stateOrder)
      } else {
        newLits.forEach { orders!!.createLiteralLevel(it, abstraction.connectivity[it] ?: 0) }
      }
      orderTime.stop()
      val currentOrders = orders!!
      val currentProvider = provider!!

      val constraint = if (applyReachConstraint) prevStateSpace else null

      // DFS_FEASIBLE stops the walk at an infeasible suffix, but only one whose refutation adds a
      // predicate: short suffixes are often infeasible for control-flow reasons alone
      val precNow = currentPrec
      val oracle: ((Trace<ExplState, ExprAction>) -> ItpRefutation?)? =
        if (traceSearch == TraceSearch.DFS_FEASIBLE && fragmentsAllowed)
          { suffix ->
            val predTrace = abstractor.toPredTrace(suffix)
            val res = traceChecker.check(predTrace)
            if (res.isFeasible) null
            else {
              val refutation = res.asInfeasible().refutation
              val candidate = dataPreds(refineWith(precNow, predTrace, refutation))
              if (candidate.size > dataPreds(precNow).size) refutation else null
            }
          }
        else null

      val iter = runIteration(model, constraint, currentOrders, currentProvider, oracle)
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

      check(iter.traces.isNotEmpty()) {
        "CEGAR iteration $i found a violation but trace generation timed out"
      }

      val refinementTime = Stopwatch.createStarted()
      var refined = currentPrec
      var usedFragment = false
      for (generated in iter.traces) {
        val trace = generated.trace
        val predTrace = abstractor.toPredTrace(trace)
        // a fragment was already found infeasible by the walk; it cannot witness a bug
        if (generated.fragmentRefutation != null) {
          usedFragment = true
          refined = refineWith(refined, predTrace, generated.fragmentRefutation)
          continue
        }
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
        refined = refineWith(refined, predTrace, res.asInfeasible().refutation)
      }
      refinementTime.stop()
      val newPrec = PredPrec.of(dataPreds(refined))
      logger.write(
        Logger.Level.MAINSTEP,
        "CEGAR refinement %d: traces=%d, traceStates=%s, checkTime=%dms, newPreds=%d\n",
        i,
        iter.traces.size,
        iter.traces.map { it.trace.states.size }.toString(),
        refinementTime.elapsedMillis(),
        newPrec.preds.size - currentPrec.preds.size,
      )
      if (usedFragment && newPrec.preds.size <= dataPreds(currentPrec).size) {
        logger.write(
          Logger.Level.MAINSTEP,
          "Trace fragment added no predicate, switching to complete counterexamples\n",
        )
        fragmentsAllowed = false
      }
      currentPrec = newPrec

      prevStateSpace = iter.stateSpace
    }
  }

  /**
   * Fresh orders; with [fullOrder], every level (ctrl vars and literals) in that order, top first.
   */
  private fun newOrders(fullOrder: List<VarDecl<*>>?): CegarOrders {
    val orders = CegarOrders(concreteModel, literalPlacement, fullOrder)
    listOf(orders.stateOrder, orders.transOrder).forEach {
      it.mddGraph.setAttribute(MddExpressionRepresentation.LOOK_AHEAD, lookAheadStrategy)
    }
    return orders
  }

  /** Control variables are tracked explicitly, so predicates over them alone are dropped. */
  private fun dataPreds(prec: PredPrec): List<Expr<BoolType>> =
    prec.preds.filter { p -> ExprUtils.getVars(p).any { it !in concreteModel.ctrlVars } }

  private fun refineWith(
    prec: PredPrec,
    predTrace: Trace<PredState, ExprAction>,
    refutation: ItpRefutation,
  ): PredPrec =
    if (adaptivePredSplit) {
      val whole = wholeRefiner.refine(prec, predTrace, refutation)
      if (whole.preds.size > prec.preds.size) whole
      else precRefiner.refine(prec, predTrace, refutation)
    } else precRefiner.refine(prec, predTrace, refutation)

  private data class IterationResult(
    val stateSpace: MddHandle,
    val violatingSize: Long,
    val stateSpaceSize: Long,
    val traces: List<GeneratedTrace>,
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
    feasibilityOracle: ((Trace<ExplState, ExprAction>) -> ItpRefutation?)?,
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
    // lifted under the current top, so the interpreter floats it over the new literal levels
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

    val traces = ArrayList<GeneratedTrace>()
    if (violatingSize != 0L) {
      // the traces of one iteration end in distinct violating states
      var excluded: MddHandle? = null
      for (k in 0 until tracesPerIteration) {
        val generated =
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
            excluded,
            traceSearch,
            feasibilityOracle,
          ) ?: break
        traces.add(generated)
        excluded = excluded?.union(generated.target) ?: generated.target
      }
    }

    return IterationResult(
      stateSpace,
      violatingSize,
      stateSpaceSize,
      traces,
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
      applyReachConstraint,
    )
  }
}

/** The events whose spans the FORCE ordering ([LiteralPlacement.FORCE]) minimizes. */
enum class ForceEvents {
  /** Per concrete transition: its ctrl vars and the literals sharing a variable with it. */
  DIRECT,
  /** Per concrete transition: its ctrl vars and the connected-literal closure of its group. */
  CLOSURE,
}

/** Where a new literal level is inserted relative to the existing literal levels. */
enum class LiteralPlacement {
  /** Newest literal highest. */
  TOP,
  /** Newest literal lowest, directly above the ctrl levels. */
  BOTTOM,
  /** The more concrete transitions a literal is connected to, the lower its level. */
  CONNECTIVITY,
  /**
   * The FORCE ordering over the abstract model, ctrl vars and literals interleaved, rebuilt from
   * scratch every iteration (no reach constraint, no cross-iteration cache reuse).
   */
  FORCE,
}

/** The state and transition orders of a run: ctrl levels at the bottom, literal levels above. */
private class CegarOrders(
  concreteModel: MonolithicExpr,
  private val literalPlacement: LiteralPlacement = LiteralPlacement.TOP,
  /**
   * A complete ordering (first = highest level) to build instead of the ctrl-at-the-bottom layout.
   */
  fullOrder: List<VarDecl<*>>? = null,
) {
  private val ctrlOffsets: Map<VarDecl<*>, Int> =
    concreteModel.ctrlVars.associateWith { concreteModel.transOffsetIndex[it] }

  /** The levels of one literal (trans: the lower, primed one of the pair). */
  private class LiteralLevels(
    val state: MddVariable,
    val transPrimed: MddVariable,
    val connectivity: Int,
  )

  // from the bottom (directly above the ctrl block) to the top
  private val literals = ArrayList<LiteralLevels>()

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
      // built bottom-up
      fullOrder.reversed().forEach {
        if (it in concreteModel.ctrlVars) createLevelOnTop(it) else createLiteralLevel(it)
      }
    } else {
      // ctrl vars at the bottom, in the concrete model's relative ordering (reversed: bottom-up)
      concreteModel
        .orderVars()
        .filter { it in concreteModel.ctrlVars }
        .reversed()
        .forEach(::createLevelOnTop)
    }
  }

  fun createLevelOnTop(v: VarDecl<*>) {
    stateOrder.createOnTop(MddVariableDescriptor.create(v.getConstDecl(0), 0))
    // ctrl vars keep their concrete offset (a promoted Boolean may be assigned several times per
    // transition); a var never assigned gets an identity
    createTransLevelOnTop(v, ctrlOffsets[v] ?: 1)
  }

  /**
   * A literal level in both orders, placed by [literalPlacement]; [connectivity] for CONNECTIVITY.
   */
  fun createLiteralLevel(v: VarDecl<*>, connectivity: Int = 0) {
    val desc0 = MddVariableDescriptor.create(v.getConstDecl(0), 0)
    val desc1 = MddVariableDescriptor.create(v.getConstDecl(1), 0)
    // the new literal's index in [literals]: everything from there up moves one level up
    val index =
      when (literalPlacement) {
        LiteralPlacement.TOP,
        LiteralPlacement.FORCE -> literals.size
        LiteralPlacement.BOTTOM -> 0
        LiteralPlacement.CONNECTIVITY -> {
          var i = 0
          while (i < literals.size && literals[i].connectivity >= connectivity) i++
          i
        }
      }
    val entry =
      if (index == literals.size) {
        val s = stateOrder.createOnTop(desc0)
        val t1 = transOrder.createOnTop(desc1)
        transOrder.createOnTop(desc0)
        LiteralLevels(s, t1, connectivity)
      } else {
        val above = literals[index]
        val s = stateOrder.createBelow(above.state, desc0)
        val t0 = transOrder.createBelow(above.transPrimed, desc0)
        val t1 = transOrder.createBelow(t0, desc1)
        LiteralLevels(s, t1, connectivity)
      }
    literals.add(index, entry)
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
