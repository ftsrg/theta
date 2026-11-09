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

import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.False
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Or
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.DssAuxVars
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.DssGeneralizerCombination
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.DssGeneralizerKind
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.DssPredicateOperators
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.DssUndecidedQueryException
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.Generalization
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.GeneralizationContext
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.Generalizers
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.computeViolationCondition
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.hasInternalCycle
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.withoutAuxVars
import hu.bme.mit.theta.xcfa.analysis.dss.decomposition.Block
import hu.bme.mit.theta.xcfa.analysis.dss.decomposition.BlockGraph
import hu.bme.mit.theta.xcfa.model.XcfaLocation

/** Blocks back from a location's entering blocks that the semantic check follows exactly. */
private const val SEMANTIC_DEPTH = 6

/**
 * Conjectures invariants for a network whose violation conditions keep drifting around a cycle of
 * blocks (dss/README.md, *Conjectured invariants*). The conditions arriving at each block entry go
 * to [generalizers]; for a generalization G at location L, the blocks starting at L assume `!G`,
 * and those ending at L must not reach G. A block that reaches G, or a may violation derived from
 * it, sends the weakest precondition on like a violation condition.
 *
 * The root reaching one means a real path breaks the conjecture; so does a chain longer than
 * [maxHops], conservatively. Both retract it everywhere, and each location has [gas] retractions.
 * Until then, quiescence is SAFE: the first time a path left `!G` at L, the block ending there
 * would have reached G from preconditions covering it, and the chain back to the root would have
 * followed that path. Sound only while this actor takes part in its network's quiescence.
 *
 * The semantic generalizer keeps a G that no path entering L from outside its cycles reaches: by
 * weakest preconditions back through acyclic blocks to the root, else by the latest summaries.
 * Which G is proposed only decides how useful it is; soundness rests on the obligations alone.
 */
class DssConjectureActor(
  override val connection: DssConnection,
  private val blockGraph: BlockGraph,
  solverFactory: SolverFactory,
  private val gas: Int,
  private val maxHops: Int = 2 * blockGraph.blocks.size,
  initialConjectures: List<Pair<XcfaLocation, Expr<BoolType>>> = emptyList(),
  generalizers: List<DssGeneralizerKind> = listOf(DssGeneralizerKind.GSPACER),
  combination: DssGeneralizerCombination = DssGeneralizerCombination.FIRST,
) : DssWorker(COORDINATOR_ID) {

  private class Live(
    val location: XcfaLocation,
    val condition: Expr<BoolType>,
    val generalization: Generalization?,
  )

  private val blocks = blockGraph.blocks.associateBy { it.id }
  private val startingAt = blockGraph.blocks.groupBy { it.initialLocation }
  private val endingAt = blockGraph.blocks.groupBy { it.finalLocation }
  private val keys = HashMap<XcfaLocation, String>()
  private val generalizer = Generalizers(generalizers, combination, gas)
  private val operators = DssPredicateOperators(solverFactory)
  private val live = LinkedHashMap<Int, Live>()
  private val liveAt = HashMap<XcfaLocation, Int>()
  private val retractionsAt = HashMap<XcfaLocation, Int>()
  private val checkable = HashMap<XcfaLocation, Boolean>()
  private val latestSummaries = HashMap<String, Expr<BoolType>>()
  private var pendingInitial: List<Pair<XcfaLocation, Expr<BoolType>>>? = initialConjectures
  private var nextId = 0
  private var shutdown = false

  var proposed = 0
    private set

  var retracted = 0
    private set

  override fun shutdownRequested(): Boolean = shutdown

  override fun processMessage(message: DssMessage): Collection<DssMessage> {
    when (message.type) {
      DssMessageType.RESULT,
      DssMessageType.EXCEPTION -> {
        shutdown = true
        return emptyList()
      }
      else -> {}
    }
    val initial =
      pendingInitial?.mapNotNull { (location, condition) ->
        if (eligible(location)) propose(location, condition) else null
      }
    pendingInitial = null
    val reply =
      when (message) {
        is DssViolationConditionMessage -> onViolationCondition(message)
        is DssConjectureFailedMessage -> onConjectureFailed(message)
        is DssPostConditionMessage -> {
          if (message.senderId in blocks) {
            latestSummaries[message.senderId] =
              if (message.postconditions.isEmpty()) False() else Or(message.postconditions)
          }
          emptyList()
        }
        else -> emptyList()
      }
    return initial.orEmpty() + reply
  }

  override fun broadcast(messages: Collection<DssMessage>) {
    val broadcaster = connection.broadcaster
    for (message in messages) {
      check(message is DssConjectureMessage) { "The conjecture actor does not send $message" }
      val targets =
        if (message.retracted) blocks.keys else message.restrictedIds + message.obligedIds
      broadcaster.broadcastToIds(message, targets)
    }
  }

  private fun onViolationCondition(message: DssViolationConditionMessage): List<DssMessage> {
    val sender = blocks[message.senderId] ?: return emptyList()
    val condition = message.violationCondition ?: return emptyList()
    val location = sender.initialLocation
    if (!eligible(location)) return emptyList()
    val key = keys.getOrPut(location) { "${keys.size}:${location.name}" }
    generalizer.record(key, condition)
    val context = GeneralizationContext(operators::isUnsat) { unreachableEntering(location, it) }
    val generalization =
      try {
        generalizer.generalize(listOf(key to condition), context)
      } catch (e: DssUndecidedQueryException) {
        null
      } ?: return emptyList()
    return listOfNotNull(propose(location, generalization.condition, generalization))
  }

  /**
   * Never the entry: the root's start there is no block's exit, so nothing would check it. No block
   * at the location may need per-path conditions, which may violations do not support.
   */
  private fun eligible(location: XcfaLocation): Boolean =
    location !in liveAt &&
      (retractionsAt[location] ?: 0) < gas &&
      checkable.getOrPut(location) {
        location != blockGraph.root.initialLocation &&
          endingAt[location].orEmpty().isNotEmpty() &&
          (startingAt[location].orEmpty() + endingAt[location].orEmpty()).none(::hasInternalCycle)
      }

  private fun propose(
    location: XcfaLocation,
    generalized: Expr<BoolType>,
    generalization: Generalization? = null,
  ): DssMessage? {
    // An invariant over havocked values would not say what it seems to
    val condition =
      if (DssAuxVars.collectVars(generalized).isEmpty()) generalized
      else withoutAuxVars(generalized) { !operators.isUnsat(it) } ?: return null
    if (condition == False()) return null
    val conjecture = nextId++
    live[conjecture] = Live(location, condition, generalization)
    liveAt[location] = conjecture
    proposed++
    return DssConjectureMessage(
      id,
      conjecture,
      condition,
      startingAt[location].orEmpty().mapTo(linkedSetOf()) { it.id },
      endingAt[location].orEmpty().mapTo(linkedSetOf()) { it.id },
      maxHops,
    )
  }

  private fun onConjectureFailed(message: DssConjectureFailedMessage): List<DssMessage> {
    val conjecture = live.remove(message.conjecture) ?: return emptyList()
    liveAt.remove(conjecture.location)
    retractionsAt.merge(conjecture.location, 1, Int::plus)
    conjecture.generalization?.let(generalizer::failed)
    retracted++
    return listOf(
      DssConjectureMessage(id, message.conjecture, conjecture.condition, retracted = true)
    )
  }

  /**
   * Whether no block entering [location] from outside its cycles reaches [condition]; the blocks on
   * a cycle through it are what the conjecture is to strengthen, so they would refute nothing.
   */
  private fun unreachableEntering(location: XcfaLocation, condition: Expr<BoolType>): Boolean {
    val onCycle = reachableFrom(startingAt[location].orEmpty())
    val entering = endingAt[location].orEmpty().filter { it.id !in onCycle }
    return entering.isNotEmpty() && entering.all { unreachableAtExit(it, condition, setOf(it.id)) }
  }

  private fun unreachableAtExit(
    block: Block,
    condition: Expr<BoolType>,
    path: Set<String>,
  ): Boolean {
    if (hasInternalCycle(block)) return summaryExcludes(block.id, condition)
    val atEntry =
      try {
        computeViolationCondition(block, mapOf(block.finalLocation to condition))
      } catch (e: InterruptedException) {
        throw e
      } catch (e: Exception) {
        return false
      }
    if (operators.isUnsat(atEntry)) return true
    if (block.isRoot) return false
    return block.predecessorIds.all { id ->
      if (id in path || path.size >= SEMANTIC_DEPTH) summaryExcludes(id, atEntry)
      else unreachableAtExit(blocks.getValue(id), atEntry, path + id)
    }
  }

  /** A block that has not sent a postcondition yet excludes nothing. */
  private fun summaryExcludes(id: String, condition: Expr<BoolType>): Boolean =
    latestSummaries[id]?.let { operators.isUnsat(And(it, condition)) } ?: false

  private fun reachableFrom(start: Collection<Block>): Set<String> {
    val reached = start.mapTo(hashSetOf()) { it.id }
    val pending = ArrayDeque(reached)
    while (pending.isNotEmpty()) {
      for (successor in blocks.getValue(pending.removeFirst()).successorIds) {
        if (reached.add(successor)) pending.addLast(successor)
      }
    }
    return reached
  }
}
