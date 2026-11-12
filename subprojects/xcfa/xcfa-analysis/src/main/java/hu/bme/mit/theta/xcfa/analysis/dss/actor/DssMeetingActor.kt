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
package hu.bme.mit.theta.xcfa.analysis.dss.actor

import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.ImmutableValuation
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.booltype.BoolExprs.False
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Or
import hu.bme.mit.theta.core.type.bvtype.BvType
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.core.type.rattype.RatExprs.Rat
import hu.bme.mit.theta.core.type.rattype.RatType
import hu.bme.mit.theta.core.utils.BvUtils
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.PathUtils
import hu.bme.mit.theta.solver.Solver
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.solver.utils.WithPushPop
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.DssAuxVars
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.DssPredicateOperators
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.withSolverConstructionLock
import hu.bme.mit.theta.xcfa.analysis.dss.decomposition.Block
import hu.bme.mit.theta.xcfa.analysis.dss.decomposition.BlockGraph
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import hu.bme.mit.theta.xcfa.model.XcfaProcedure
import java.math.BigInteger

/**
 * One direction's network; [originalOf] maps its locations to the program's (not synthetic ones).
 * The postconditions of [uncertified] blocks are ignored, e.g. a bounded checker's, whose path
 * variables would be conflated across runs; no location they end at is ever certified.
 */
class DssMeetingSide(
  val blockGraph: BlockGraph,
  val originalOf: Map<XcfaLocation, XcfaLocation>,
  val uncertified: Set<String> = emptySet(),
)

/** Exact conditions of both directions met in [state] at the entry of their blocks. */
data class DssMeet(
  val forwardBlock: String,
  val forwardCondition: Expr<BoolType>,
  val backwardBlock: String,
  val backwardCondition: Expr<BoolType>,
  val state: Valuation,
)

/**
 * Combines a forward and a backward network of [program]. Both directions' violation conditions are
 * exact, so where they intersect at one location, the program is UNSAFE ([meet]).
 *
 * A converged region certifies the summaries at the locations it covers. Where both directions'
 * certified summaries are disjoint, no error path passes; if those locations cut every path from
 * the entry to an error, the program is SAFE. A failing query disables only this actor.
 */
class DssMeetingActor(
  override val connection: DssConnection,
  private val program: XcfaProcedure,
  forward: DssMeetingSide,
  backward: DssMeetingSide,
  solverFactory: SolverFactory,
  private val sharedVars: Set<VarDecl<*>>,
  private val shareInvariants: Boolean = true,
  fallbackSolverFactory: SolverFactory? = null,
) : DssWorker(COORDINATOR_ID) {

  private val forwardSide = Side(forward)
  private val backwardSide = Side(backward)
  private val operators = DssPredicateOperators(solverFactory, fallbackSolverFactory)
  private val modelSolver = lazy { withSolverConstructionLock { solverFactory.createSolver() } }
  private val unsatCache = HashMap<Expr<BoolType>, Boolean>()
  private var shutdown = false

  @Volatile
  var meet: DssMeet? = null
    private set

  /** Why this actor stopped helping, if it did. */
  @Volatile
  var failure: Throwable? = null
    private set

  private class Side(val spec: DssMeetingSide) {
    val blocks: Map<String, Block> = spec.blockGraph.blocks.associateBy { it.id }
    val endingAt = spec.blockGraph.blocks.groupBy { it.finalLocation }
    val startingAt = spec.blockGraph.blocks.groupBy { it.initialLocation }
    val localOf: Map<XcfaLocation, XcfaLocation> =
      spec.originalOf.entries.associate { (local, original) -> original to local }
    /** States inside a block pass there unseen by any block boundary summary. */
    val inner: Set<XcfaLocation> =
      spec.blockGraph.blocks.flatMapTo(hashSetOf()) {
        it.locations - it.initialLocation - it.finalLocation
      }
    val latest = HashMap<String, DssPostConditionMessage>()
    val history = HashMap<String, HashMap<Int, Expr<BoolType>>>()
    val violations = HashMap<XcfaLocation, MutableList<Pair<String, Expr<BoolType>>>>()
    val sent = HashMap<XcfaLocation, Expr<BoolType>>()
    val covers = HashMap<Triple<String, Int, Int>, Boolean>()
  }

  override fun shutdownRequested(): Boolean = shutdown

  override fun processMessage(message: DssMessage): Collection<DssMessage> {
    when (message.type) {
      DssMessageType.RESULT -> {
        shutdown = true
        if (modelSolver.isInitialized()) runCatching { modelSolver.value.close() }
        return emptyList()
      }
      DssMessageType.EXCEPTION -> {
        // A failed network's messages stay valid; only a failure outside the networks ends this
        if (sideOf(message.senderId) == null) shutdown = true
        return emptyList()
      }
      else -> {}
    }
    if (failure != null) return emptyList()
    return try {
      when (message) {
        is DssPostConditionMessage -> onPostCondition(message)
        is DssViolationConditionMessage -> onViolationCondition(message)
        else -> emptyList()
      }
    } catch (e: InterruptedException) {
      throw e
    } catch (e: Exception) {
      failure = e
      emptyList()
    }
  }

  override fun broadcast(messages: Collection<DssMessage>) {
    val broadcaster = connection.broadcaster
    for (message in messages) {
      when (message) {
        is DssResultMessage -> broadcaster.broadcastToAll(message)
        is DssRestrictionMessage -> broadcaster.broadcastToIds(message, message.targetIds)
        else -> error("The meeting actor does not send $message")
      }
    }
  }

  private fun sideOf(sender: String): Side? =
    when (sender) {
      in forwardSide.blocks -> forwardSide
      in backwardSide.blocks -> backwardSide
      else -> null
    }

  private fun onViolationCondition(message: DssViolationConditionMessage): List<DssMessage> {
    val side = sideOf(message.senderId) ?: return emptyList()
    val condition = message.violationCondition ?: return emptyList()
    val entry = side.blocks.getValue(message.senderId).initialLocation
    val location = side.spec.originalOf[entry] ?: return emptyList()
    val known = side.violations.getOrPut(location) { mutableListOf() }
    if (known.any { it.second == condition }) return emptyList()
    known += message.senderId to condition
    val other = if (side === forwardSide) backwardSide else forwardSide
    val opposite = other.violations[location].orEmpty()
    if (opposite.isEmpty()) return emptyList()
    val offset = DssAuxVars.nextIndex(condition)
    val any = And(condition, Or(opposite.map { DssAuxVars.shift(it.second, offset) }))
    if (model(any) == null) return emptyList()
    for ((otherId, otherCondition) in opposite) {
      val state = model(And(condition, DssAuxVars.shift(otherCondition, offset))) ?: continue
      meet =
        if (side === forwardSide)
          DssMeet(message.senderId, condition, otherId, otherCondition, state)
        else DssMeet(otherId, otherCondition, message.senderId, condition, state)
      return listOf(DssResultMessage(id, DssResult.UNSAFE))
    }
    return emptyList()
  }

  private fun onPostCondition(message: DssPostConditionMessage): List<DssMessage> {
    val side = sideOf(message.senderId) ?: return emptyList()
    if (message.senderId in side.spec.uncertified) return emptyList()
    side.latest[message.senderId] = message
    side.history.getOrPut(message.senderId) { HashMap() }[message.version] = formulaOf(message)
    val forwardInvariants = certified(forwardSide)
    val backwardInvariants = certified(backwardSide)
    if (cutsEveryErrorPath(forwardInvariants, backwardInvariants)) {
      return listOf(DssResultMessage(id, DssResult.SAFE))
    }
    if (!shareInvariants) return emptyList()
    return exchange(forwardSide, backwardSide, forwardInvariants) +
      exchange(backwardSide, forwardSide, backwardInvariants)
  }

  private fun formulaOf(message: DssPostConditionMessage): Expr<BoolType> =
    if (message.postconditions.isEmpty()) False() else Or(message.postconditions)

  /** The certified summaries of [side], by its own locations. */
  private fun certified(side: Side): Map<XcfaLocation, Expr<BoolType>> {
    val region = side.latest.keys.filterTo(hashSetOf()) { coversInputs(side, it) }
    while (
      region.removeIf { id -> side.blocks.getValue(id).predecessorIds.any { it !in region } }
    ) {
      // Until every member's predecessors are members
    }
    return side.endingAt
      .filter { (location, ending) -> location !in side.inner && ending.all { it.id in region } }
      .mapValues { (_, ending) -> Or(ending.map { formulaOf(side.latest.getValue(it.id)) }) }
  }

  /** Whether the latest postcondition of [id] was computed from states covering the newest ones. */
  private fun coversInputs(side: Side, id: String): Boolean {
    val message = side.latest.getValue(id)
    return side.blocks.getValue(id).predecessorIds.all { predecessor ->
      val used = message.inputs[predecessor] ?: return@all false
      val newest = side.latest[predecessor] ?: return@all false
      if (used == newest.version || formulaOf(newest) == False()) return@all true
      val usedStates = side.history[predecessor]?.get(used) ?: return@all false
      side.covers.getOrPut(Triple(predecessor, used, newest.version)) {
        operators.isLeq(formulaOf(newest), usedStates)
      }
    }
  }

  /**
   * Whether no path from the entry to an error avoids the locations no error path passes: those
   * that cannot reach an error, and those where the certified summaries are disjoint.
   */
  private fun cutsEveryErrorPath(
    forwardInvariants: Map<XcfaLocation, Expr<BoolType>>,
    backwardInvariants: Map<XcfaLocation, Expr<BoolType>>,
  ): Boolean {
    if (forwardInvariants.isEmpty() && backwardInvariants.isEmpty()) return false
    fun closed(location: XcfaLocation): Boolean {
      val backwardLocal = backwardSide.localOf[location] ?: return true
      val reachable = forwardSide.localOf[location]?.let(forwardInvariants::get)
      val reachesError = backwardInvariants[backwardLocal]
      if (reachable != null && isUnsat(reachable)) return true
      if (reachesError != null && isUnsat(reachesError)) return true
      return reachable != null &&
        reachesError != null &&
        isUnsat(And(reachable, DssAuxVars.shift(reachesError, DssAuxVars.nextIndex(reachable))))
    }
    if (closed(program.initLoc)) return true
    if (program.initLoc.error) return false
    val reached = hashSetOf(program.initLoc)
    val pending = ArrayDeque(listOf(program.initLoc))
    while (pending.isNotEmpty()) {
      for (edge in pending.removeFirst().outgoingEdges) {
        val next = edge.target
        if (next in reached || closed(next)) continue
        if (next.error) return false
        reached += next
        pending.addLast(next)
      }
    }
    return true
  }

  private fun exchange(
    from: Side,
    to: Side,
    invariants: Map<XcfaLocation, Expr<BoolType>>,
  ): List<DssMessage> {
    val messages = mutableListOf<DssMessage>()
    for ((fromLocation, invariant) in invariants) {
      val location = from.spec.originalOf[fromLocation] ?: continue
      val toLocation = to.localOf[location]?.takeIf { it !in to.inner } ?: continue
      val targets = to.startingAt[toLocation]?.map { it.id } ?: continue
      val decls = ExprUtils.getVars(invariant) + ExprUtils.getConstants(invariant)
      if (!decls.all { it is VarDecl<*> && it in sharedVars }) continue
      val previous = to.sent[toLocation] ?: True()
      if (operators.isLeq(previous, invariant)) continue
      to.sent[toLocation] = And(previous, invariant)
      messages += DssRestrictionMessage(id, invariant, targets.toSet())
    }
    return messages
  }

  private fun isUnsat(expr: Expr<BoolType>): Boolean =
    unsatCache.getOrPut(expr) { operators.isUnsat(expr) }

  /** A satisfying state of [expr] over [sharedVars], or null unless the solver says SAT. */
  private fun model(expr: Expr<BoolType>): Valuation? {
    val solver: Solver = modelSolver.value
    WithPushPop(solver).use {
      solver.add(PathUtils.unfold(expr, 0))
      if (!solver.check().isSat) return null
      val found = PathUtils.extractValuation(solver.model, 0).toMap()
      val state = ImmutableValuation.builder()
      for (decl in sharedVars) {
        @Suppress("UNCHECKED_CAST")
        val value = (found[decl] ?: defaultValue(decl.type)) as LitExpr<Type>? ?: continue
        state.put(decl as VarDecl<Type>, value)
      }
      return state.build()
    }
  }

  /** Variables the model leaves free: one value for both directions' witness paths. */
  private fun defaultValue(type: Type): LitExpr<*>? =
    when (type) {
      is IntType -> Int(0)
      is BoolType -> False()
      is RatType -> Rat(0, 1)
      is BvType -> BvUtils.bigIntegerToNeutralBvLitExpr(BigInteger.ZERO, type.size)
      else -> null
    }
}
