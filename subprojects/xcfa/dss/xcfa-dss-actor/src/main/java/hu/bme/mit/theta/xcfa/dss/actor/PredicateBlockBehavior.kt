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
package hu.bme.mit.theta.xcfa.dss.actor

import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.False
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Not
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Or
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.solver.SolverManager
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaPrec
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.analysis.reverseMapping
import hu.bme.mit.theta.xcfa.dss.analysis.BlockXcfaExtraction
import hu.bme.mit.theta.xcfa.dss.analysis.CheckerFactory
import hu.bme.mit.theta.xcfa.dss.analysis.DssAuxVars
import hu.bme.mit.theta.xcfa.dss.analysis.DssCheckerRoster
import hu.bme.mit.theta.xcfa.dss.analysis.DssPredicateOperators
import hu.bme.mit.theta.xcfa.dss.analysis.collectAssumePreds
import hu.bme.mit.theta.xcfa.dss.analysis.collectPreds
import hu.bme.mit.theta.xcfa.dss.analysis.combinePredPrecs
import hu.bme.mit.theta.xcfa.dss.analysis.computePathViolationCondition
import hu.bme.mit.theta.xcfa.dss.analysis.computeViolationCondition
import hu.bme.mit.theta.xcfa.dss.analysis.extractBlockXcfa
import hu.bme.mit.theta.xcfa.dss.analysis.getPredPrec
import hu.bme.mit.theta.xcfa.dss.analysis.hasInternalCycle
import hu.bme.mit.theta.xcfa.dss.analysis.packPostcondition
import hu.bme.mit.theta.xcfa.dss.analysis.runWorkerConfig
import hu.bme.mit.theta.xcfa.dss.decomposition.Block
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.XcfaEdge
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import hu.bme.mit.theta.xcfa.model.XcfaProcedure
import hu.bme.mit.theta.xcfa.passes.changeVars

/** Legacy Z3: its interpolation handles C integer arithmetic, but it is not thread-safe. */
const val DEFAULT_DSS_SOLVER = "Z3"

/** The solver of the concurrent executor, which needs a thread-safe one. */
const val CONCURRENT_DSS_SOLVER = "Z3:new"

/** CPAchecker's `DssBlockAnalysis`, running a Theta checker on the extracted block. */
class PredicateBlockBehavior(
  private val wholeProgram: XCFA,
  private val sourceProcedure: XcfaProcedure,
  private val block: Block,
  private val checkerRoster: DssCheckerRoster,
  private val useGlobalPredicatePool: Boolean = true,
  private val resetPrecisionForEveryRun: Boolean = false,
  private val reuseBlockPrecision: Boolean = false,
  private val checkerFallback: Boolean = false,
  private val solverFactory: SolverFactory? = null,
) : DssBlockBehavior {

  private data class Summary(
    val state: Expr<BoolType>,
    val precision: Set<Expr<BoolType>>,
    val nonTrivialForEachPredecessor: Boolean = false,
  ) {
    val isTop: Boolean
      get() = state == True()
  }

  private sealed interface RunResult {
    data class Safe(val postcondition: Expr<BoolType>, val precision: Set<Expr<BoolType>>) :
      RunResult

    data class Unsafe(val path: PathViolation?) : RunResult
  }

  private data class PathViolation(
    val condition: Expr<BoolType>,
    val reachedReceivedViolation: Boolean,
    val edges: List<XcfaEdge>,
  )

  private val usesPathViolations: Boolean by lazy { hasInternalCycle(block) }

  private val pathViolationsSoFar = linkedSetOf<Expr<BoolType>>()

  private data class AnalysisResult(
    val summaries: List<Summary>,
    val violationCondition: Expr<BoolType>?,
  )

  private val operators by lazy {
    DssPredicateOperators(solverFactory ?: SolverManager.resolveSolverFactory(DEFAULT_DSS_SOLVER))
  }

  private val startPrecision: Set<Expr<BoolType>> by lazy {
    if (useGlobalPredicatePool) wholeProgram.collectAssumePreds() else emptySet()
  }

  private var fastestChecker: Int? = null

  private val ownPrecision = linkedSetOf<Expr<BoolType>>()

  private val preconditions = LinkedHashMap<String, MutableList<Summary>>()
  private val violationConditions = LinkedHashMap<String, MutableList<Expr<BoolType>>>()
  private val relevant = mutableListOf<Summary>()
  private var containsViolationInsideBlock = false
  private val reportedFromTop = mutableSetOf<Expr<BoolType>>()

  private val ownTargets: List<XcfaLocation> = block.locations.filter { it.error }

  private val invariantsByStart = HashMap<Expr<BoolType>, Map<XcfaLocation, List<Expr<BoolType>>>>()
  private val violationRecords = mutableListOf<DssViolationRecord>()
  private val reportedViolationConditions = mutableListOf<Expr<BoolType>>()

  override fun initialMessages(): Collection<DssMessage> = runInitialAnalysis()

  override fun onPostCondition(message: DssPostConditionMessage): Collection<DssMessage> =
    if (storePrecondition(message)) analyzePrecondition() else emptyList()

  override fun onViolationCondition(message: DssViolationConditionMessage): Collection<DssMessage> =
    if (storeViolationCondition(message)) analyzeViolationCondition(message.senderId)
    else emptyList()

  private fun top() = Summary(True(), startPrecision)

  fun runInitialAnalysis(): Collection<DssMessage> {
    return when (val result = run(top(), violationCondition = null)) {
      is RunResult.Safe ->
        if (result.postcondition == False()) emptyList()
        else reportPostconditions(listOf(Summary(result.postcondition, result.precision)))
      is RunResult.Unsafe -> {
        containsViolationInsideBlock = true
        buildList {
          // Stand-in for CPAchecker's "block end reached": a Theta checker stops at the first cex
          if (block.successorIds.isNotEmpty()) {
            add(DssPostConditionMessage(block.id, listOf(True()), startPrecision))
          }
          addAll(
            result.path?.let {
              violationRecords += DssPathViolation(it.condition, it.edges, false, emptyList())
              reportViolationCondition(accumulatePathViolations(listOf(it.condition)))
            } ?: reportViolationConditions(targetsOfOwnViolations())
          )
        }
      }
    }
  }

  /** Returns whether the analysis should proceed (CPAchecker's `shouldProceed`). */
  fun storePrecondition(message: DssPostConditionMessage): Boolean {
    relevant.clear()
    val received =
      message.postconditions.map { state ->
        Summary(state, message.precision, message.nonTrivialForEachPredecessor)
      }
    val sender = message.senderId
    val stored = preconditions[sender]
    if (stored.isNullOrEmpty()) {
      preconditions[sender] = received.toMutableList()
      relevant.addAll(received)
      appendTopToRelevantIfNecessary(sender)
      return true
    }
    for (new in received) {
      var isRelevant = true
      for (old in stored.toList()) {
        if (operators.isLeq(new.state, old.state)) {
          stored.remove(old)
        }
        if (isRelevant && operators.isLeq(old.state, new.state)) {
          isRelevant = false
        }
      }
      if (isRelevant) relevant.add(new)
      stored.add(new)
    }
    if (relevant.isNotEmpty()) appendTopToRelevantIfNecessary(sender)
    return relevant.isNotEmpty()
  }

  private fun appendTopToRelevantIfNecessary(sender: String) {
    if (preconditions.keys.size != block.predecessorIds.size) {
      relevant.add(top())
      return
    }
    for ((other, states) in preconditions) {
      if (other == sender) continue
      if (states.any { it.isTop }) {
        relevant.add(top())
        return
      }
    }
  }

  /** Returns false if the condition is unsatisfiable or repeats the sender's last one. */
  fun storeViolationCondition(message: DssViolationConditionMessage): Boolean {
    val condition =
      requireNotNull(message.violationCondition) { "Expected a violation condition in $message" }
    val sender = message.senderId
    val old = violationConditions.remove(sender).orEmpty().toSet()
    if (operators.isUnsat(condition)) return false
    violationConditions[sender] = mutableListOf(condition)
    return condition !in old
  }

  fun analyzePrecondition(): Collection<DssMessage> {
    if (!containsViolationInsideBlock && violationConditions.isEmpty()) {
      return emptyList()
    }
    val received =
      violationConditions.flatMap { (sender, conditions) -> conditions.map { sender to it } }
    val result = analyzeViolationCondition(received, checkOnlyRelevant = true)
    return reportViolationCondition(result.violationCondition) +
      reportPostconditions(result.summaries)
  }

  fun analyzeViolationCondition(sender: String): Collection<DssMessage> {
    relevant.clear()
    val violations = violationConditions[sender]
    require(!violations.isNullOrEmpty()) { "No violation condition found for sender ID: $sender" }
    val result =
      analyzeViolationCondition(violations.map { sender to it }, checkOnlyRelevant = false)
    return reportPostconditions(result.summaries) +
      reportViolationCondition(result.violationCondition)
  }

  private fun analyzeViolationCondition(
    received: List<Pair<String, Expr<BoolType>>>,
    checkOnlyRelevant: Boolean,
  ): AnalysisResult {
    val violations = received.map { it.second }
    if (preconditions.isEmpty() && !block.isRoot) {
      return AnalysisResult(emptyList(), null)
    }

    val hasNonTrivialSummariesForEachPredecessor =
      preconditions.isNotEmpty() && preconditions.values.all { states -> states.any { !it.isTop } }

    val startStates = linkedSetOf<Summary>()
    if (checkOnlyRelevant) {
      startStates.addAll(relevant)
    } else if (preconditions.isNotEmpty()) {
      for (state in preconditions.values.flatten()) {
        // SCC rule: skip only top states; skipping non-top states derived from top is unsound
        if (
          hasNonTrivialSummariesForEachPredecessor &&
            state.nonTrivialForEachPredecessor &&
            state.isTop
        ) {
          continue
        }
        startStates.add(state)
      }
    } else {
      startStates.add(top())
    }

    // Non-top first: a top summary would otherwise deduplicate the others away
    val orderedStartStates = startStates.sortedBy { it.isTop }
    val violationCondition = if (violations.isEmpty()) null else Or(violations)
    val summaries = mutableListOf<Summary>()
    var targetReached = false
    var reportReceivedViolations = false
    val pathViolations = mutableListOf<Expr<BoolType>>()
    var analyzedTrivial = false
    for (start in orderedStartStates) {
      if (start.isTop && analyzedTrivial) continue
      analyzedTrivial = analyzedTrivial || start.isTop
      val precision =
        if (resetPrecisionForEveryRun || start.isTop) startPrecision
        else combinePrecisionIfPossible() ?: start.precision
      // Without the start state's atoms, the block-end abstraction can forget the precondition
      val startState = start.copy(precision = precision + listOf(start.state).collectPreds())

      when (val result = run(startState, violationCondition)) {
        is RunResult.Safe -> {
          if (result.postcondition != False()) {
            summaries +=
              Summary(
                result.postcondition,
                result.precision,
                hasNonTrivialSummariesForEachPredecessor,
              )
          }
        }
        is RunResult.Unsafe -> {
          // The checker stopped at the cex, so the postcondition needs a run without targets
          val summary = run(startState, violationCondition = null, keepSpecificationTargets = false)
          if (summary is RunResult.Safe && summary.postcondition != False()) {
            summaries +=
              Summary(
                summary.postcondition,
                summary.precision,
                hasNonTrivialSummariesForEachPredecessor,
              )
          }
          targetReached = true
          // CPAchecker assumes a vc reached from top was already sent; that fails if it arrived
          // before any precondition
          val reportReceived =
            violations.isNotEmpty() &&
              (!checkOnlyRelevant ||
                startStates.size == 1 ||
                !start.isTop ||
                violationCondition !in reportedFromTop)
          if (reportReceived) {
            reportReceivedViolations = true
            if (start.isTop && violationCondition != null) reportedFromTop += violationCondition
          }
          result.path
            ?.takeIf { !it.reachedReceivedViolation || reportReceived }
            ?.let {
              pathViolations += it.condition
              violationRecords +=
                DssPathViolation(
                  it.condition,
                  it.edges,
                  it.reachedReceivedViolation,
                  if (it.reachedReceivedViolation) received else emptyList(),
                )
            }
        }
      }
    }

    if (!targetReached) return AnalysisResult(summaries, null)
    if (usesPathViolations) {
      val condition = accumulatePathViolations(pathViolations)
      return AnalysisResult(summaries, condition)
    }
    // The cex does not tell which target it reached, so the condition covers all of them
    val targets = buildMap {
      if (containsViolationInsideBlock) putAll(targetsOfOwnViolations())
      if (reportReceivedViolations && violationCondition != null) {
        put(block.finalLocation, violationCondition)
      }
    }
    val newViolationCondition =
      targets
        .takeIf { it.isNotEmpty() }
        ?.let { computeViolationCondition(block, it) }
        ?.also { condition ->
          val used = if (reportReceivedViolations) received else emptyList()
          violationRecords += DssAllPathsViolation(condition, targets, used)
        }
    return AnalysisResult(summaries, newViolationCondition)
  }

  private fun targetsOfOwnViolations(): Map<XcfaLocation, Expr<BoolType>> =
    ownTargets.associateWith { True() }

  private fun combinePrecisionIfPossible(): Set<Expr<BoolType>>? {
    if (preconditions.isEmpty()) return null
    return combinePredPrecs(preconditions.values.flatten().map { it.precision }) + startPrecision
  }

  private fun run(
    start: Summary,
    violationCondition: Expr<BoolType>?,
    keepSpecificationTargets: Boolean = true,
  ): RunResult {
    val extraction =
      extractBlockXcfa(
        sourceProcedure,
        block,
        precondition = start.state.takeUnless { start.isTop },
        violationCondition = violationCondition,
        keepSpecificationTargets = keepSpecificationTargets,
      )
    val initialPredicates =
      if (reuseBlockPrecision) start.precision + ownPrecision else start.precision
    val initialPrecision = initialPredicates.takeIf { it.isNotEmpty() }?.let(::getPredPrec)
    val result = runWithCheckerFallback { checker ->
      runWorkerConfig(extraction.xcfa, checker, initialPrecision).also {
        check(it.isSafe || it.isUnsafe) { "Inconclusive block analysis result: $it" }
      }
    }
    if (reuseBlockPrecision) {
      (result.prec.orElse(null) as? XcfaPrec<*>)?.let { ownPrecision += it.collectPreds() }
    }
    if (result.isUnsafe) {
      return RunResult.Unsafe(
        if (usesPathViolations) pathViolation(result.asUnsafe().cex, extraction) else null
      )
    }
    val proof = result.asSafe().proof
    invariantsByStart[start.state] =
      proof
        .getPartitions()
        .entries
        .mapNotNull { (clone, states) -> extraction.originalLocations[clone]?.let { it to states } }
        .groupBy({ it.first }, { it.second })
        .mapValues { (_, states) -> states.flatten().map { it.toExpr() }.distinct() }
    val reached = proof.getPartitions().values.flatten().map { it.toExpr() }
    return RunResult.Safe(
      normalize(packPostcondition(result, extraction.exitLocation)),
      reached.collectPreds() + start.precision,
    )
  }

  private fun pathViolation(
    cex: Trace<XcfaState<PtrState<*>>, XcfaAction>,
    extraction: BlockXcfaExtraction,
  ): PathViolation {
    val actions = cex.actions
    check(actions.isNotEmpty() && actions.last().target.error) {
      "Block ${block.id}: counterexample does not end in an error location: $actions"
    }
    val originalOf =
      cex.states
        .flatMap { state -> state.processes.values.flatMap { it.varLookup } }
        .fold(mapOf<VarDecl<*>, VarDecl<*>>()) { acc, lookup -> acc + lookup.reverseMapping() }
    fun XcfaAction.isOn(edge: XcfaEdge?) =
      edge != null && source == edge.source && target == edge.target
    val path = actions.drop(actions.indexOfFirst { it.isOn(extraction.preconditionEdge) } + 1)
    val condition = computePathViolationCondition(path.map { it.label.changeVars(originalOf) })
    val unknown =
      ExprUtils.getVars(condition).filterNot { it in programVars || DssAuxVars.isAux(it) }
    check(unknown.isEmpty()) {
      "Block ${block.id}: path violation condition over unknown variables $unknown: $condition"
    }
    val clonesByEnds = extraction.originalEdges.keys.groupBy { it.source to it.target }
    val edges =
      path.mapNotNull { action ->
        val clones = clonesByEnds[action.source to action.target].orEmpty()
        val clone =
          clones.singleOrNull()
            ?: clones.firstOrNull { it.label == action.label.changeVars(originalOf) }
        clone?.let(extraction.originalEdges::get)
      }
    return PathViolation(condition, actions.last().isOn(extraction.violationConditionEdge), edges)
  }

  /** Predecessors keep only the last condition per sender, so refuted paths must stay in. */
  private fun accumulatePathViolations(new: Collection<Expr<BoolType>>): Expr<BoolType>? {
    if (new.isEmpty()) return null
    pathViolationsSoFar += new
    return Or(pathViolationsSoFar)
  }

  private val programVars: Set<VarDecl<*>> by lazy {
    sourceProcedure.vars + wholeProgram.globalVars.map { it.wrappedVar }
  }

  private inline fun <T> runWithCheckerFallback(analysis: (CheckerFactory) -> T): T {
    val leader = fastestChecker
    if (checkerRoster.ranksPerBlock && leader == null) return runEveryChecker(analysis)
    val order = leader?.let { listOf(it) + (0 until checkerRoster.size).filter { i -> i != it } }
    val attempts = order?.size ?: if (checkerFallback) checkerRoster.size else 1
    var failure: Exception? = null
    repeat(attempts) { attempt ->
      val index = order?.get(attempt)
      try {
        return analysis(if (index != null) checkerRoster[index] else checkerRoster.next(attempt))
      } catch (e: InterruptedException) {
        throw e
      } catch (e: Exception) {
        failure?.addSuppressed(e) ?: run { failure = e }
      }
    }
    throw checkNotNull(failure)
  }

  private inline fun <T> runEveryChecker(analysis: (CheckerFactory) -> T): T {
    var failure: Exception? = null
    var fastest = -1
    var fastestNanos = Long.MAX_VALUE
    var fastestResult: T? = null
    repeat(checkerRoster.size) { index ->
      val start = System.nanoTime()
      try {
        val result = analysis(checkerRoster[index])
        val nanos = System.nanoTime() - start
        if (nanos < fastestNanos) {
          fastest = index
          fastestNanos = nanos
          fastestResult = result
        }
      } catch (e: InterruptedException) {
        throw e
      } catch (e: Exception) {
        failure?.addSuppressed(e) ?: run { failure = e }
      }
    }
    if (fastest < 0) throw checkNotNull(failure)
    fastestChecker = fastest
    @Suppress("UNCHECKED_CAST") return fastestResult as T
  }

  /** Valid states become `true`, as CPAchecker's BDD abstractions do. */
  private fun normalize(state: Expr<BoolType>): Expr<BoolType> {
    val simplified = ExprUtils.simplify(state)
    return if (simplified != False() && operators.isUnsat(Not(simplified))) True() else simplified
  }

  private fun reportPostconditions(summaries: List<Summary>): Collection<DssMessage> {
    if (summaries.isEmpty()) return emptyList()
    val unique = deduplicateStates(summaries)
    return listOf(
      DssPostConditionMessage(
        block.id,
        unique.map { it.state },
        unique.flatMapTo(linkedSetOf()) { it.precision },
        unique.any { it.nonTrivialForEachPredecessor },
      )
    )
  }

  private fun deduplicateStates(summaries: List<Summary>): List<Summary> {
    if (summaries.size < 2) return summaries
    val kept = mutableListOf<Summary>()
    for (summary in summaries) {
      if (kept.none { operators.isLeq(summary.state, it.state) }) {
        kept += summary
      }
    }
    return kept
  }

  private fun reportViolationConditions(
    targets: Map<XcfaLocation, Expr<BoolType>>
  ): Collection<DssMessage> {
    val condition = computeViolationCondition(block, targets)
    violationRecords += DssAllPathsViolation(condition, targets, emptyList())
    return reportViolationCondition(condition)
  }

  private fun reportViolationCondition(condition: Expr<BoolType>?): Collection<DssMessage> {
    if (condition == null || condition == False()) return emptyList()
    if (block.isRoot && operators.isUnsat(condition)) return emptyList()
    reportedViolationConditions += condition
    return listOf(DssViolationConditionMessage(block.id, condition))
  }

  override fun witness(): DssBlockWitness =
    DssBlockWitness(invariants(), violationRecords.toList(), reportedViolationConditions.toList())

  /** Invariants from start states that cover the block's real entries, else from top. */
  private fun invariants(): Map<XcfaLocation, List<Expr<BoolType>>>? {
    val stored = preconditions.values.flatten().map { it.state }.distinct()
    val cover =
      when {
        !block.isRoot &&
          preconditions.keys.containsAll(block.predecessorIds) &&
          stored.isNotEmpty() &&
          stored.all { it in invariantsByStart } -> stored
        True() in invariantsByStart -> listOf(True())
        else -> return null
      }
    return cover
      .flatMap { invariantsByStart.getValue(it).entries }
      .groupBy({ it.key }, { it.value })
      .mapValues { (_, states) -> states.flatten().distinct() }
  }
}
