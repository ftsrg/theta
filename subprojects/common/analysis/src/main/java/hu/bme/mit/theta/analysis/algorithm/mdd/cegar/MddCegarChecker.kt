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
import hu.bme.mit.delta.java.mdd.impl.MddStructuralTemplate
import hu.bme.mit.delta.mdd.MddInterpreter
import hu.bme.mit.delta.mdd.MddVariableDescriptor
import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.algorithm.bounded.ImplicitPredicateAbstractor
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr
import hu.bme.mit.theta.analysis.algorithm.bounded.action
import hu.bme.mit.theta.analysis.algorithm.bounded.orderVars
import hu.bme.mit.theta.analysis.algorithm.mdd.varordering.orderVarsFromRandomStartingPoints
import hu.bme.mit.theta.analysis.algorithm.mdd.result.MddAnalysisStatistics
import hu.bme.mit.theta.analysis.algorithm.mdd.result.MddProof
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.AbstractNextStateDescriptor
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.impl.AndNextStateDescriptor
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.impl.MddNodeNextStateDescriptor
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.impl.MddNodePostcondition
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.impl.OnTheFlyReachabilityNextStateDescriptor
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.impl.OrNextStateDescriptor
import hu.bme.mit.theta.analysis.algorithm.mdd.node.expression.ExprLatticeDefinition
import hu.bme.mit.theta.analysis.algorithm.mdd.node.expression.MddExpressionRepresentation
import hu.bme.mit.theta.analysis.algorithm.mdd.node.expression.MddExpressionTemplate
import hu.bme.mit.theta.analysis.algorithm.mdd.trace.GeneratedTrace
import hu.bme.mit.theta.analysis.algorithm.mdd.trace.TraceSearch
import hu.bme.mit.theta.analysis.algorithm.mdd.trace.generateTrace
import hu.bme.mit.theta.analysis.algorithm.mdd.fixedpoint.IterationStrategy
import hu.bme.mit.theta.analysis.algorithm.mdd.fixedpoint.StateSpaceEnumerationProvider
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
  // the property only: the init expression as a predicate mentions every variable, so its literal
  // connects every other literal to every transition and defeats the per-group relation split
  private val initPrec: (MonolithicExpr) -> PredPrec = { model ->
    PredPrec.of(listOf(model.propExpr))
  },
  private val precRefiner: PrecRefiner<PredState, ExprAction, PredPrec, ItpRefutation> =
    JoiningPrecRefiner.create(ItpRefToPredPrec(ExprSplitters.atoms())),
  private val useReachConstraint: Boolean = true,
  private val useOnTheFlyReachability: Boolean = false,
  private val traceTimeout: Long = 10,
  // the lower bound: cache the previous iteration's witnesses into this iteration's nodes
  private val useTransitionSeeding: Boolean = false,
  // the upper bound: prune by the previous relation's visited edges (needs the seeding infrastructure)
  private val useTransitionBound: Boolean = useTransitionSeeding,
  private val lookAheadStrategy: MddExpressionRepresentation.MddToExprStrategy =
    MddExpressionRepresentation.MddToExprStrategy.NONE,
  private val proofStrategy: MddExpressionRepresentation.MddToExprStrategy =
    MddExpressionRepresentation.MddToExprStrategy.NODE_LEVEL,
  // build the abstract relation per group of concrete transitions with identical connected literals
  private val splitRelation: Boolean = true,
  // check the counterexample with the transition fired at each step instead of the whole relation
  private val perStepRefinement: Boolean = true,
  // where new literal levels go relative to the existing ones (BOTTOM disables seeding, whose lifts
  // assume the newest literals on top)
  private val literalPlacement: LiteralPlacement = LiteralPlacement.TOP,
  // how many counterexamples (ending in distinct violating states) to refine with per iteration
  private val tracesPerIteration: Int = 1,
  // drop the saturation and SAT caches before every iteration (bounded memory, no cross-iteration reuse)
  private val clearCaches: Boolean = false,
  // refine with whole interpolants first and fall back to [precRefiner] only when that adds nothing
  private val adaptivePredSplit: Boolean = false,
  // the events the FORCE ordering minimizes the spans of
  private val forceEvents: ForceEvents = ForceEvents.DIRECT,
  // flip the FORCE ordering: its top becomes the bottom
  private val forceReverse: Boolean = false,
  // how the abstract counterexample is searched backward from the violating states
  private val traceSearch: TraceSearch = TraceSearch.DFS,
) : SafetyChecker<MddProof, Trace<ExplState, ExprAction>, UnitPrec> {

  private val wholeRefiner: PrecRefiner<PredState, ExprAction, PredPrec, ItpRefutation> =
    JoiningPrecRefiner.create(ItpRefToPredPrec(ExprSplitters.whole()))

  private val seedingEnabled = useTransitionSeeding && literalPlacement == LiteralPlacement.TOP
  private val boundEnabled = useTransitionBound && seedingEnabled

  // the transition bound (upper) subsumes the reach-set constraint's source pruning, so the reach
  // constraint is dropped when it is used; witness caching (lower) is the orthogonal seeding knob.
  // FORCE placement rebuilds the orders every iteration, and the previous reach set, a node of the
  // old orders, cannot be carried over
  private val applyReachConstraint =
    useReachConstraint && !boundEnabled && literalPlacement != LiteralPlacement.FORCE

  init {
    require(!useTransitionBound || useTransitionSeeding) {
      "the transition bound needs the witness-order infrastructure of transition seeding"
    }
    require(!(useOnTheFlyReachability && (useReachConstraint || useTransitionBound))) {
      "on-the-fly reachability is sound only without an upper bound: it cannot combine with the " +
        "reach-set constraint or the transition bound (early termination leaves the bound unsound)"
    }
  }

  override fun check(prec: UnitPrec?): SafetyResult<MddProof, Trace<ExplState, ExprAction>> {
    val totalTime = Stopwatch.createStarted()

    // FORCE placement creates its orders per iteration, once the abstract model is known
    var orders: CegarOrders? =
      if (literalPlacement == LiteralPlacement.FORCE) null else newOrders(null)
    val seed =
      if (seedingEnabled)
        SeedKnowledge(
          transitionBinding(concreteModel),
          orders!!.transDataBoundary,
          orders.stateDataBoundary,
          orders.transBoundOrder,
          orders.stateBoundOrder,
          solverPool,
          logger,
        )
      else null

    val abstractor = ImplicitPredicateAbstractor(concreteModel, splitRelation, perStepRefinement)
    val traceChecker = traceCheckerFactory(concreteModel)
    var currentPrec = initPrec(concreteModel)
    var prevStateSpace: MddHandle? = null

    // one provider for the whole run: its saturation/relProd caches are keyed by (node, descriptor),
    // so a refined relation never gets a false hit, while the unchanged concrete sub-structure is
    // reused across iterations; the graph cleanup listener prunes entries whose nodes have died
    var provider: StateSpaceEnumerationProvider? =
      orders?.let { iterationStrategy.createProvider(it.stateOrder) }

    var totalSolverCalls = 0L
    var i = 0
    // a fragment refines but does not have to add a predicate; if one ever fails to, complete traces
    // are used from then on, so the loop cannot spin on the same abstraction
    var fragmentsAllowed = true

    while (true) {
      i++
      if (clearCaches && i > 1 && orders != null) {
        provider!!.clear()
        listOfNotNull(orders.stateOrder, orders.transOrder, orders.stateExprOrder).forEach {
          it.mddGraph.getAttribute(MddExpressionTemplate.SAT_CACHE)?.clear()
        }
      }
      val abstraction = abstractor.abstractModel(currentPrec)
      val model = abstraction.model
      val newLits = abstraction.newLiterals

      val orderTime = Stopwatch.createStarted()
      if (literalPlacement == LiteralPlacement.FORCE) {
        // the FORCE ordering of the abstract model's variables (ctrl vars and literals interleaved;
        // events: the concrete transitions with their connected literals); the levels of an existing
        // order cannot be permuted, so the orders, graphs and caches are rebuilt from scratch
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

      // Concretize a suffix on demand: this is what stops the feasibility-driven walk. An infeasible
      // suffix is only worth stopping for if it actually refines. Short suffixes near the error are
      // routinely infeasible for control-flow reasons alone, and predicates over control variables
      // are dropped (those variables are tracked explicitly), so such a suffix would end the walk
      // and teach nothing. Keep walking until the refutation adds a predicate.
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

      val iter =
        runIteration(
          model,
          constraint,
          currentOrders,
          seed,
          newLits,
          abstractor.literalToPred,
          currentProvider,
          oracle,
        )
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
          // the checked trace's actions are the concrete per-step actions already
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
        // the fragment taught us nothing; fall back to complete counterexamples for the rest of the run
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

  /** Fresh orders; with [fullOrder], every level (ctrl vars and literals) in that order, top first. */
  private fun newOrders(fullOrder: List<VarDecl<*>>?): CegarOrders {
    val orders =
      CegarOrders(concreteModel, seedingEnabled, boundEnabled, literalPlacement, fullOrder)
    listOfNotNull(orders.stateOrder, orders.transOrder, orders.stateExprOrder).forEach {
      it.mddGraph.setAttribute(MddExpressionRepresentation.LOOK_AHEAD, lookAheadStrategy)
    }
    return orders
  }

  /** The predicates that survive into the next precision: control variables are tracked explicitly. */
  private fun dataPreds(prec: PredPrec): List<Expr<BoolType>> =
    prec.preds.filter { p -> ExprUtils.getVars(p).any { it !in concreteModel.ctrlVars } }

  private fun refineWith(
    prec: PredPrec,
    predTrace: Trace<PredState, ExprAction>,
    refutation: ItpRefutation,
  ): PredPrec =
    if (adaptivePredSplit) {
      // whole interpolants keep the literal count low; atoms only when they bring nothing new
      val whole = wholeRefiner.refine(prec, predTrace, refutation)
      if (whole.preds.size > prec.preds.size) whole else precRefiner.refine(prec, predTrace, refutation)
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
    seed: SeedKnowledge?,
    newLits: List<VarDecl<BoolType>>,
    literalToPred: Map<Decl<*>, Expr<BoolType>>,
    provider: StateSpaceEnumerationProvider,
    feasibilityOracle: ((Trace<ExplState, ExprAction>) -> ItpRefutation?)? = null,
  ): IterationResult {
    val stateSig: MddSignature = orders.stateOrder.defaultSetSignature
    val transSig: MddSignature = orders.transOrder.defaultSetSignature
    val stateExprSig: MddSignature? = orders.stateExprOrder?.defaultSetSignature
    // the bounds live in mirror orders; their current top floats a bound built last iteration over
    // this iteration's new literal levels, exactly as the source top would
    val transBoundSig: MddSignature? = orders.transBoundOrder?.defaultSetSignature
    val stateBoundSig: MddSignature? = orders.stateBoundOrder?.defaultSetSignature
    // the on-the-fly kill switch fires on reaching a terminal below the prop node, which a
    // node with concrete witness levels never does
    val propSeedable = stateExprSig != null && !useOnTheFlyReachability

    // build + seed the three node kinds. the abstract init and relation are non-empty whenever the
    // concrete ones are (the v⟺pred literal definitions are always satisfiable), so their root
    // satisfiability check is skippable; the prop node has no such guarantee and stays checked
    val initNode = stateNode(PathUtils.unfold(model.initExpr, 0), stateExprSig ?: stateSig, true)
    seed?.init?.seed(listOf(initNode), newLits, literalToPred)

    val relSolverBefore = solverPool.checkCount
    val transNodes =
      model.split.map { expr ->
        val transExpr =
          And(PathUtils.unfold(expr, VarIndexingFactory.indexing(0)), And(orders.identityExprs))
        transSig.topVariableHandle.checkInNode(
          MddExpressionTemplate.ofKnownSat(transExpr, { it as Decl<*> }, solverPool, true)
        )
      }
    seed?.trans?.seed(transNodes, newLits, literalToPred)

    val propNode =
      stateNode(
        PathUtils.unfold(Not(model.propExpr), 0),
        if (propSeedable) stateExprSig!! else stateSig,
      )
    if (propSeedable) seed?.prop?.seed(listOf(propNode), newLits, literalToPred)
    val relSolverCalls = solverPool.checkCount - relSolverBefore

    val relationOr =
      OrNextStateDescriptor.create(transNodes.map { MddNodeNextStateDescriptor.of(it) })
    // lift each bound under the current top so the interpreter floats it over the literal levels
    // added since it was built, then AND it onto the relation
    val nextStates =
      listOfNotNull(
          prevStateSpace?.let {
            MddNodePostcondition.of(stateSig.topVariableHandle.getHandleFor(it.node))
          },
          seed?.trans?.bound?.let {
            MddNodeNextStateDescriptor.of(transBoundSig!!.topVariableHandle.getHandleFor(it.node))
          },
          relationOr,
        )
        .reduce(AndNextStateDescriptor::of)

    val effectiveNextStates =
      if (useOnTheFlyReachability)
        OnTheFlyReachabilityNextStateDescriptor.of(nextStates, propNode)
      else nextStates

    val satSolverBefore = solverPool.checkCount
    val ssgTime = Stopwatch.createStarted()
    val stateSpace =
      provider.compute(
        boundedInitializer(
          initNode,
          seed?.init?.bound?.let { stateBoundSig!!.topVariableHandle.getHandleFor(it.node) },
        ),
        effectiveNextStates,
        stateSig.topVariableHandle,
      )
    ssgTime.stop()
    val satSolverCalls = solverPool.checkCount - satSolverBefore

    val propViolating =
      if (propSeedable) filterStates(stateSpace, propNode, seed?.prop?.bound)
      else stateSpace.intersection(propNode)
    val violatingSize = MddInterpreter.calculateNonzeroCount(propViolating)
    val stateSpaceSize = MddInterpreter.calculateNonzeroCount(stateSpace)

    val traces = ArrayList<GeneratedTrace>()
    if (violatingSize != 0L) {
      // trace generation does set operations between state sets and the taller init node, so the
      // init node is brought to a state-order set: reachable ∩ init = init (init ⊆ reachable)
      val traceInitNode =
        if (stateExprSig != null) filterStates(stateSpace, initNode, seed?.init?.bound)
        else initNode
      // several traces per iteration end in distinct violating states; each is refined separately
      var excluded: MddHandle? = null
      for (k in 0 until tracesPerIteration) {
        val generated =
          generateTrace(
            transNodes,
            transSig,
            stateSpace,
            propViolating,
            traceInitNode,
            stateSig,
            model,
            traceTimeout,
            logger,
            orders.transDataBoundary,
            excluded,
            traceSearch,
            feasibilityOracle,
          ) ?: break
        traces.add(generated)
        excluded = excluded?.union(generated.target) ?: generated.target
      }
    }

    // after trace generation, so its probes land in the extracted bounds too
    if (seed != null) {
      seed.trans.update()
      seed.init.update()
      if (propSeedable) seed.prop.update()
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

  /**
   * The saturation initializer for [node], restricted by [boundLift] — its previous-iteration bound,
   * already lifted to the current top — an over-approximation, so this only changes the exploration
   * effort, not the set.
   */
  private fun boundedInitializer(
    node: MddHandle,
    boundLift: MddHandle?,
  ): AbstractNextStateDescriptor.Postcondition {
    val nodeInit = MddNodePostcondition.of(node)
    val boundInit = boundLift?.let { MddNodePostcondition.of(it) }
    return if (boundInit != null) AndNextStateDescriptor.of(boundInit, nodeInit) else nodeInit
  }

  /**
   * `states ∩ exprNode` when [exprNode] lives in the taller state-expression order, which delta set
   * ops cannot combine with state-order handles. The get() probes cache witnesses into [exprNode];
   * keys the accumulated [bound] knows absent are skipped unprobed.
   */
  private fun filterStates(states: MddHandle, exprNode: MddHandle, bound: MddHandle?): MddHandle {
    if (states.isTerminalZero || exprNode.isTerminalZero || bound?.isTerminalZero == true)
      return states.variableHandle.mddGraph.terminalZeroHandle
    if (states.isTerminal) return states
    val boundEff = if (bound != null && bound.isTerminal) null else bound
    val traceInfo = states.variableHandle.variable.orElseThrow().traceInfo
    val boundAligned =
      boundEff != null && boundEff.variableHandle.variable.orElseThrow().traceInfo == traceInfo
    val templateBuilder = JavaMddFactory.getDefault().createUnsafeTemplateBuilder()
    val cursor = states.cursor()
    while (cursor.moveNext()) {
      val childBound: MddHandle?
      if (boundAligned) {
        val child = boundEff!!.node.get(cursor.key()) ?: boundEff.node.defaultValue()
        if (child == null || child == boundEff.variableHandle.mddGraph.terminalZeroNode) continue
        childBound = boundEff.variableHandle.lower.orElseThrow().getHandleFor(child)
      } else childBound = boundEff
      val filtered = filterStates(cursor.value() as MddHandle, exprNode.get(cursor.key()), childBound)
      if (!filtered.isTerminalZero) templateBuilder.set(cursor.key(), filtered.node)
    }
    return states.variableHandle.checkInNode(
      MddStructuralTemplate.of(templateBuilder.buildAndReset())
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

/**
 * The variable orders of one CEGAR run and their lockstep growth: literal levels are added on top
 * per refinement, above the ctrl levels and — with seeding — the concrete witness levels at the
 * bottom of the trans and state-expression orders.
 */
/** The events whose spans the FORCE ordering ([LiteralPlacement.FORCE]) minimizes. */
enum class ForceEvents {
  /** Per concrete transition: its ctrl vars and the literals sharing a variable with it. */
  DIRECT,
  /**
   * Per concrete transition: its ctrl vars and the connected-literal closure of its group, i.e. the
   * literal levels its abstract transition node actually spans.
   */
  CLOSURE,
}

/** Where a new literal level is inserted relative to the existing literal levels. */
enum class LiteralPlacement {
  /** Newest literal highest (the seeding lifts depend on this). */
  TOP,
  /** Newest literal lowest, directly above the ctrl levels. */
  BOTTOM,
  /**
   * Literal levels sorted by connectivity: the more concrete transitions a literal is connected to,
   * the lower its level (a widely used literal raises the top of many transition nodes wherever it
   * is, so it goes low; a rarely used one goes high, raising few).
   */
  CONNECTIVITY,
  /**
   * The FORCE variable ordering heuristic over the abstract model, ctrl vars and literals interleaved,
   * recomputed and rebuilt from scratch every iteration (the reach constraint and cross-iteration
   * cache reuse are lost; seeding is disabled).
   */
  FORCE,
}

private class CegarOrders(
  concreteModel: MonolithicExpr,
  useTransitionSeeding: Boolean,
  useTransitionBound: Boolean,
  private val literalPlacement: LiteralPlacement = LiteralPlacement.TOP,
  // a complete ordering of the ctrl vars and literals (first = highest level) to build instead of
  // the ctrl-block-at-the-bottom layout; used by FORCE placement
  fullOrder: List<VarDecl<*>>? = null,
) {
  // the concrete relation offsets of the ctrl vars, consulted when their trans levels are created
  private val ctrlOffsets: Map<VarDecl<*>, Int> =
    concreteModel.ctrlVars.associateWith { concreteModel.transOffsetIndex[it] }

  /** The levels one literal occupies in the orders (trans levels: the lower, primed one of the pair). */
  private class LiteralLevels(
    val state: MddVariable,
    val stateExpr: MddVariable?,
    val stateBound: MddVariable?,
    val transPrimed: MddVariable,
    val transBoundPrimed: MddVariable?,
    val connectivity: Int,
  )

  // the literal levels from the bottom (directly above the ctrl block) to the top
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
  // init and prop nodes go to their own order with concrete witness levels at the bottom, so
  // their exploration caches full witnesses and they can be seeded like the relation
  val stateExprOrder: MddVariableOrder? =
    if (useTransitionSeeding)
      JavaMddFactory.getDefault().createMddVariableOrder(ExprLatticeDefinition.forExpr())
    else null
  // the extracted bounds live in fresh mirror graphs growing in lockstep with the trans /
  // state-expression orders: checking the structural bound nodes into the source graphs would
  // collide them with the procedural expression nodes there and force solver-driven equality
  // enumeration during canonization
  val transBoundOrder: MddVariableOrder? =
    if (useTransitionBound)
      JavaMddFactory.getDefault().createMddVariableOrder(ExprLatticeDefinition.forExpr())
    else null
  val stateBoundOrder: MddVariableOrder? =
    if (useTransitionBound)
      JavaMddFactory.getDefault().createMddVariableOrder(ExprLatticeDefinition.forExpr())
    else null
  val identityExprs = mutableListOf<Expr<BoolType>>()

  // topmost concrete witness level of each order; bound extraction cuts here, keeping the
  // bounds over the abstract levels that saturation consults
  var transDataBoundary: Any? = null
    private set

  var stateDataBoundary: Any? = null
    private set

  init {
    if (fullOrder != null) {
      require(!useTransitionSeeding) { "a full ordering has no place for the witness levels" }
      // built bottom-up; literals go on top of whatever is below them
      fullOrder.reversed().forEach {
        if (it in concreteModel.ctrlVars) createLevelOnTop(it) else createLiteralLevel(it)
      }
    } else initCtrlAtBottom(concreteModel, useTransitionSeeding)
  }

  private fun initCtrlAtBottom(concreteModel: MonolithicExpr, useTransitionSeeding: Boolean) {
    // ctrl vars sit at the bottom, in the concrete model's relative ordering
    val orderedVars = concreteModel.orderVars()
    val ctrlOrdered = orderedVars.filter { it in concreteModel.ctrlVars }
    val dataOrdered = orderedVars.filter { it !in concreteModel.ctrlVars }

    if (useTransitionSeeding) {
      // concrete witness levels sit below all abstract levels; the state order does not get them
      dataOrdered.reversed().forEach {
        createTransLevelOnTop(it, concreteModel.transOffsetIndex[it])
        createStateExprLevelOnTop(MddVariableDescriptor.create(it.getConstDecl(0), 0))
      }
      transDataBoundary =
        transOrder.defaultSetSignature.topVariableHandle.variable.map { it.traceInfo }.orElse(null)
      stateDataBoundary =
        stateExprOrder!!
          .defaultSetSignature
          .topVariableHandle
          .variable
          .map { it.traceInfo }
          .orElse(null)
    }
    // createOnTop builds bottom-up, so reverse to keep ctrlOrdered[0] highest within the block
    ctrlOrdered.reversed().forEach(::createLevelOnTop)
  }

  /**
   * Top-insertion: new literal levels go above the ctrl and witness levels. The bound lift depends on
   * this — placed elsewhere, the skip-level handle would stop being a pure default-edge lift.
   */
  fun createLevelOnTop(v: VarDecl<*>) {
    stateOrder.createOnTop(MddVariableDescriptor.create(v.getConstDecl(0), 0))
    createStateExprLevelOnTop(MddVariableDescriptor.create(v.getConstDecl(0), 0))
    // ctrl vars keep their concrete offset (1 for the XCFA location and edge variables; a promoted
    // Boolean may be assigned several times per transition); a var never assigned gets an identity
    createTransLevelOnTop(v, ctrlOffsets[v] ?: 1)
  }

  /**
   * A new literal level in every order, placed according to [literalPlacement]; [connectivity] is the
   * number of concrete transitions the literal is connected to (used by CONNECTIVITY placement).
   */
  fun createLiteralLevel(v: VarDecl<*>, connectivity: Int = 0) {
    val desc0 = MddVariableDescriptor.create(v.getConstDecl(0), 0)
    val desc1 = MddVariableDescriptor.create(v.getConstDecl(1), 0)
    // index in [literals] the new literal takes: everything from that index up moves one level up
    val index =
      when (literalPlacement) {
        LiteralPlacement.TOP -> literals.size
        LiteralPlacement.BOTTOM -> 0
        LiteralPlacement.CONNECTIVITY -> {
          var i = 0
          while (i < literals.size && literals[i].connectivity >= connectivity) i++
          i
        }
        // the full ordering is built bottom-up, so each literal goes on top
        LiteralPlacement.FORCE -> literals.size
      }
    val entry =
      if (index == literals.size) {
        // on top of every existing level; pairs keep v0 above v1 (built bottom-up)
        val s = stateOrder.createOnTop(desc0)
        val se = stateExprOrder?.createOnTop(desc0)
        val sb = stateBoundOrder?.createOnTop(desc0)
        val t1 = transOrder.createOnTop(desc1)
        transOrder.createOnTop(desc0)
        val tb1 =
          transBoundOrder?.let {
            val x = it.createOnTop(desc1)
            it.createOnTop(desc0)
            x
          }
        LiteralLevels(s, se, sb, t1, tb1, connectivity)
      } else {
        // directly below the literal currently at [index]
        val above = literals[index]
        val s = stateOrder.createBelow(above.state, desc0)
        val se = stateExprOrder?.createBelow(above.stateExpr!!, desc0)
        val sb = stateBoundOrder?.createBelow(above.stateBound!!, desc0)
        val t0 = transOrder.createBelow(above.transPrimed, desc0)
        val t1 = transOrder.createBelow(t0, desc1)
        val tb1 =
          transBoundOrder?.let {
            val x0 = it.createBelow(above.transBoundPrimed!!, desc0)
            it.createBelow(x0, desc1)
          }
        LiteralLevels(s, se, sb, t1, tb1, connectivity)
      }
    literals.add(index, entry)
  }

  private fun createTransLevelOnTop(v: VarDecl<*>, targetIndex: Int) {
    val domainSize = 0
    if (targetIndex > 0) {
      addTransLevel(MddVariableDescriptor.create(v.getConstDecl(targetIndex), domainSize))
    } else {
      addTransLevel(MddVariableDescriptor.create(v.getConstDecl(1), domainSize))
      identityExprs.add(Eq(v.getConstDecl(0).ref, v.getConstDecl(1).ref))
    }
    addTransLevel(MddVariableDescriptor.create(v.getConstDecl(0), domainSize))
  }

  // the trans / state-expression orders and their bound mirrors grow in lockstep, so a bound built
  // at one iteration's top lifts over later literal levels exactly as the source node does
  private fun addTransLevel(desc: MddVariableDescriptor) {
    transOrder.createOnTop(desc)
    transBoundOrder?.createOnTop(desc)
  }

  private fun createStateExprLevelOnTop(desc: MddVariableDescriptor) {
    stateExprOrder?.createOnTop(desc)
    stateBoundOrder?.createOnTop(desc)
  }
}
