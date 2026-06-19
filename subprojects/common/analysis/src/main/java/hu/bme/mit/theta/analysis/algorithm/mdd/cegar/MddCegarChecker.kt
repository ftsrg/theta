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
import hu.bme.mit.theta.analysis.algorithm.mdd.trace.generateTrace
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
  // the lower bound: cache the previous iteration's witnesses into this iteration's nodes
  private val useTransitionSeeding: Boolean = false,
  // the upper bound: prune by the previous relation's SAT cache (needs the seeding infrastructure)
  private val useTransitionBound: Boolean = useTransitionSeeding,
  private val lookAheadStrategy: MddExpressionRepresentation.MddToExprStrategy =
    MddExpressionRepresentation.MddToExprStrategy.NONE,
  private val proofStrategy: MddExpressionRepresentation.MddToExprStrategy =
    MddExpressionRepresentation.MddToExprStrategy.NODE_LEVEL,
) : SafetyChecker<MddProof, Trace<ExplState, ExprAction>, UnitPrec> {

  // the transition bound (upper) subsumes the reach-set constraint's source pruning, so the reach
  // constraint is dropped when it is used; witness caching (lower) is the orthogonal seeding knob
  private val applyReachConstraint = useReachConstraint && !useTransitionBound

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

    val orders = CegarOrders(concreteModel, useTransitionSeeding, useTransitionBound)
    orders.stateOrder.mddGraph.setAttribute(MddExpressionRepresentation.LOOK_AHEAD, lookAheadStrategy)
    orders.transOrder.mddGraph.setAttribute(MddExpressionRepresentation.LOOK_AHEAD, lookAheadStrategy)
    orders.stateExprOrder?.mddGraph?.setAttribute(
      MddExpressionRepresentation.LOOK_AHEAD,
      lookAheadStrategy,
    )
    val seed =
      if (useTransitionSeeding)
        SeedKnowledge(
          transitionBinding(concreteModel),
          orders.transDataBoundary,
          orders.stateDataBoundary,
          orders.transBoundOrder,
          orders.stateBoundOrder,
          logger,
        )
      else null

    val abstractor = ImplicitPredicateAbstractor(concreteModel)
    val traceChecker = traceCheckerFactory(concreteModel)
    var currentPrec = initPrec(concreteModel)
    var prevStateSpace: MddHandle? = null

    var totalSolverCalls = 0L
    var i = 0

    while (true) {
      i++
      val (model, newLits) = abstractor.abstractModel(currentPrec)

      newLits.forEach(orders::createLevelOnTop)

      val constraint = if (applyReachConstraint) prevStateSpace else null

      val iter = runIteration(model, constraint, orders, seed, newLits, abstractor.literalToPred)
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
    seed: SeedKnowledge?,
    newLits: List<VarDecl<BoolType>>,
    literalToPred: Map<Decl<*>, Expr<BoolType>>,
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

    // build + seed the three node kinds
    val initNode = stateNode(PathUtils.unfold(model.initExpr, 0), stateExprSig ?: stateSig)
    seed?.init?.seed(listOf(initNode), newLits, literalToPred)

    val relSolverBefore = solverPool.checkCount
    val transNodes =
      model.split.map { expr ->
        val transExpr =
          And(PathUtils.unfold(expr, VarIndexingFactory.indexing(0)), And(orders.identityExprs))
        transSig.topVariableHandle.checkInNode(
          MddExpressionTemplate.of(transExpr, { it as Decl<*> }, solverPool, true)
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
    val provider = iterationStrategy.createProvider(stateSig.variableOrder)
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

    val trace =
      if (violatingSize != 0L) {
        // trace generation does set operations between state sets and the taller init node, so the
        // init node is brought to a state-order set: reachable ∩ init = init (init ⊆ reachable)
        val traceInitNode =
          if (stateExprSig != null) filterStates(stateSpace, initNode, seed?.init?.bound)
          else initNode
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
        )
      } else null

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
      trace,
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

  private fun stateNode(expr: Expr<BoolType>, sig: MddSignature): MddHandle =
    sig.topVariableHandle.checkInNode(MddExpressionTemplate.of(expr, { it as Decl<*> }, solverPool))

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
private class CegarOrders(
  concreteModel: MonolithicExpr,
  useTransitionSeeding: Boolean,
  useTransitionBound: Boolean,
) {

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
    // abstract vars (ctrl vars and literals) always have offset 1 in the abstract relation
    createTransLevelOnTop(v, 1)
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
