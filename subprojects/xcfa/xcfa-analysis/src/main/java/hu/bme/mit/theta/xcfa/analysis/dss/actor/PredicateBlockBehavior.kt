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

import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.False
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Not
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Or
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.solver.SolverManager
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaPrec
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.BlockXcfaExtraction
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.CheckerFactory
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.DssAuxVars
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.DssCheckerRoster
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.DssPredicateOperators
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.DssUndecidedQueryException
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.ViolationGeneralizer
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.collectAssumePreds
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.collectPreds
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.combinePredPrecs
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.computePathViolationCondition
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.computeViolationCondition
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.extractBlockXcfa
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.getPredPrec
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.hasInternalCycle
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.packPostcondition
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.runWorkerConfig
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.withoutAuxVars
import hu.bme.mit.theta.xcfa.analysis.dss.decomposition.Block
import hu.bme.mit.theta.xcfa.analysis.reverseMapping
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.XcfaEdge
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import hu.bme.mit.theta.xcfa.model.XcfaProcedure
import hu.bme.mit.theta.xcfa.passes.changeVars

/** Legacy Z3: its interpolation handles C integer arithmetic, but it is not thread-safe. */
const val DEFAULT_DSS_SOLVER = "Z3"

/** The solver of the concurrent executor, which needs a thread-safe one. */
const val CONCURRENT_DSS_SOLVER = "Z3:new"

/**
 * CPAchecker's `DssBlockAnalysis`, running a Theta checker on the extracted block.
 *
 * With [trackSummaries], postconditions carry their version and inputs, and an analysis without
 * exit states reports `false` to the observers, so `DssMeetingActor` can certify converged regions.
 * A restriction (`DssRestrictionMessage`) is conjoined to every start state; violation conditions
 * stay exact, as they are computed from the block's own paths only. [finishing] marks one of its
 * network's `finishingBlocks`, which a finisher checker may analyze.
 *
 * With a positive [generalizationGas], a start state is first analyzed against a generalization of
 * the received conditions ([ViolationGeneralizer]). Only its SAFE result is used: refuting the
 * weaker target refutes the received conditions too. Its UNSAFE result is discarded.
 */
class PredicateBlockBehavior(
  private val wholeProgram: XCFA,
  private val sourceProcedure: XcfaProcedure,
  private val block: Block,
  checkerRoster: DssCheckerRoster,
  private val useGlobalPredicatePool: Boolean = true,
  private val resetPrecisionForEveryRun: Boolean = false,
  private val reuseBlockPrecision: Boolean = false,
  private val checkerFallback: Boolean = false,
  private val solverFactory: SolverFactory? = null,
  private val trackSummaries: Boolean = false,
  finishing: Boolean = false,
  generalizationGas: Int = 0,
) : DssBlockBehavior {

  private val checkerRoster = checkerRoster.forBlock(finishing)

  private val generalizer = generalizationGas.takeIf { it > 0 }?.let(::ViolationGeneralizer)

  private val statistics = DssBlockStatistics()

  private data class Summary(val state: Expr<BoolType>, val precision: Set<Expr<BoolType>>) {
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

  /**
   * Whether the last analysis found a new error path: then the block's other paths are still to be
   * searched, also when the predecessor answers with an unchanged postcondition.
   */
  private var pathsPending = false

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
  private var containsViolationInsideBlock = false

  private val ownTargets: List<XcfaLocation> = block.locations.filter { it.error }

  private val invariantsByStart = HashMap<Expr<BoolType>, Map<XcfaLocation, List<Expr<BoolType>>>>()
  private val violationRecords = mutableListOf<DssViolationRecord>()
  private val reportedViolationConditions = mutableListOf<Expr<BoolType>>()

  /** The conjunction of all received restrictions; only ever strengthened. */
  private var restriction: Expr<BoolType> = True()
  private var postconditionVersion = 0
  private val inputVersions = LinkedHashMap<String, Int>()
  private val restrictedInputs = HashSet<String>()

  /** Exit states under a restriction cover the error paths only: no program invariant. */
  private val restricted: Boolean
    get() = restriction != True() || restrictedInputs.isNotEmpty()

  override fun initialMessages(): Collection<DssMessage> = runInitialAnalysis()

  override fun onPostCondition(message: DssPostConditionMessage): Collection<DssMessage> =
    if (storePrecondition(message) || pathsPending) analyzePrecondition() else emptyList()

  override fun onViolationCondition(message: DssViolationConditionMessage): Collection<DssMessage> =
    if (storeViolationCondition(message)) analyzeViolationCondition(message.senderId)
    else emptyList()

  /** A stronger start state can only refute more, so only received conditions are re-analyzed. */
  override fun onRestriction(message: DssRestrictionMessage): Collection<DssMessage> {
    if (operators.isLeq(restriction, message.restriction)) return emptyList()
    restriction = And(restriction, message.restriction)
    val canAnalyze = block.isRoot || preconditions.isNotEmpty()
    return if (violationConditions.isNotEmpty() && canAnalyze) analyzePrecondition()
    else emptyList()
  }

  private fun top() = Summary(True(), startPrecision)

  /**
   * Explores the block from top. Only the root publishes the postcondition, as top is its real
   * precondition; elsewhere a postcondition from top would feed itself back through a loop.
   */
  fun runInitialAnalysis(): Collection<DssMessage> {
    return when (val result = run(top(), violationCondition = null)) {
      is RunResult.Safe ->
        if (!block.isRoot) emptyList()
        else
          reportPostconditions(
            listOf(Summary(result.postcondition, result.precision)).filter { it.state != False() }
          )
      is RunResult.Unsafe -> {
        containsViolationInsideBlock = true
        result.path?.let {
          violationRecords += DssPathViolation(it.condition, it.edges, false, emptyList())
          reportViolationCondition(accumulatePathViolations(listOf(it.condition)))
        } ?: reportViolationConditions(targetsOfOwnViolations())
      }
    }
  }

  /**
   * CPAchecker's `AlwaysReplacePreconditionHandler`: the message replaces everything stored from
   * its sender; returns whether the analysis should proceed, i.e. whether the states changed.
   */
  fun storePrecondition(message: DssPostConditionMessage): Boolean {
    val received = message.postconditions.map { Summary(it, message.precision) }
    inputVersions[message.senderId] = message.version
    if (message.restricted) restrictedInputs += message.senderId
    else restrictedInputs -= message.senderId
    val stored = preconditions.put(message.senderId, received.toMutableList())
    return stored == null || !statesEqual(received, stored)
  }

  /**
   * Whether both lists cover the same entry states. CPAchecker matches the states pairwise, but
   * Theta's states are not canonical: the same union can arrive split differently every round.
   */
  private fun statesEqual(states1: List<Summary>, states2: List<Summary>): Boolean {
    val union1 = Or(states1.map { it.state })
    val union2 = Or(states2.map { it.state })
    return operators.isLeq(union1, union2) && operators.isLeq(union2, union1)
  }

  /** Returns false if the condition is unsatisfiable or repeats the sender's last one. */
  fun storeViolationCondition(message: DssViolationConditionMessage): Boolean {
    val condition =
      requireNotNull(message.violationCondition) { "Expected a violation condition in $message" }
    val sender = message.senderId
    statistics.violationConditionsReceived++
    val old = violationConditions.remove(sender).orEmpty().toSet()
    if (operators.isUnsat(condition)) return false
    violationConditions[sender] = mutableListOf(condition)
    generalizer?.record(sender, condition)
    return condition !in old
  }

  /**
   * Also without a violation condition: on a cycle of blocks nobody else would start the others.
   */
  fun analyzePrecondition(): Collection<DssMessage> {
    val received =
      violationConditions.flatMap { (sender, conditions) -> conditions.map { sender to it } }
    val result = analyzeViolationCondition(received)
    return reportViolationCondition(result.violationCondition) +
      reportPostconditions(result.summaries)
  }

  fun analyzeViolationCondition(sender: String): Collection<DssMessage> {
    val violations = violationConditions[sender]
    require(!violations.isNullOrEmpty()) { "No violation condition found for sender ID: $sender" }
    val result = analyzeViolationCondition(violations.map { sender to it })
    return reportPostconditions(result.summaries) +
      reportViolationCondition(result.violationCondition)
  }

  /**
   * Runs the block analysis with [received] attached at the block exit from every stored
   * precondition, as CPAchecker's `AlwaysReplaceExplorationEngine` does: a postcondition replaces
   * its sender's earlier ones, so it must cover all of them. While a predecessor has not sent
   * anything, a speculative run from top looks for violations only; its postcondition is dropped.
   */
  private fun analyzeViolationCondition(
    received: List<Pair<String, Expr<BoolType>>>
  ): AnalysisResult {
    val violations = received.map { it.second }
    val startStates = linkedSetOf<Summary>()
    startStates.addAll(preconditions.values.flatten())
    if (block.isRoot) startStates.add(top())
    // Non-top first: a top summary would otherwise deduplicate the others away
    val orderedStartStates = startStates.sortedBy { it.isTop }.map { it to false }.toMutableList()
    val speculative =
      !block.isRoot &&
        !preconditions.keys.containsAll(block.predecessorIds) &&
        startStates.none { it.isTop }
    if (speculative) orderedStartStates += top() to true
    val violationCondition = if (violations.isEmpty()) null else Or(violations)
    var generalization = generalizationOf(received)
    val summaries = mutableListOf<Summary>()
    var targetReached = false
    var reportReceivedViolations = false
    val pathViolations = mutableListOf<Expr<BoolType>>()
    var analyzedTrivial = false
    for ((start, discardSummary) in orderedStartStates) {
      if (start.isTop && analyzedTrivial) continue
      analyzedTrivial = analyzedTrivial || start.isTop
      val precision =
        if (resetPrecisionForEveryRun || start.isTop) startPrecision
        else combinePrecisionIfPossible() ?: start.precision
      // Without the start state's atoms, the block-end abstraction can forget the precondition
      val startAtoms = listOf(start.state, restriction).collectPreds()
      val startState = start.copy(precision = precision + startAtoms)

      // A speculative run looks for violations only, which a probe cannot find
      val probe = generalization?.takeUnless { discardSummary }
      if (probe != null && violationCondition != null) {
        statistics.probes++
        val probeStart =
          startState.copy(precision = startState.precision + listOf(probe.condition).collectPreds())
        val result =
          try {
            run(probeStart, Or(violationCondition, probe.condition), probe = true)
          } catch (e: InterruptedException) {
            throw e
          } catch (e: Exception) {
            // The exact run below decides; a probe must not fail an analysis that would succeed
            RunResult.Unsafe(null)
          }
        if (result is RunResult.Safe) {
          statistics.probesRefuted++
          if (result.postcondition != False()) {
            summaries += Summary(result.postcondition, result.precision)
          }
          continue
        }
        statistics.probesFailed++
        generalizer?.failed(probe)
        generalization = null
      }

      when (val result = run(startState, violationCondition)) {
        is RunResult.Safe -> {
          if (!discardSummary && result.postcondition != False()) {
            summaries += Summary(result.postcondition, result.precision)
          }
        }
        is RunResult.Unsafe -> {
          // The checker stopped at the cex, so the postcondition needs a run without targets
          if (!discardSummary) {
            val summary =
              run(startState, violationCondition = null, keepSpecificationTargets = false)
            // Dropping these states would leave the postcondition short of what its inputs name
            check(summary is RunResult.Safe) {
              "Block ${block.id}: the run without targets reached an error location: $summary"
            }
            if (summary.postcondition != False()) {
              summaries += Summary(summary.postcondition, summary.precision)
            }
          }
          targetReached = true
          // Never suppressed: the predecessor replaces its stored condition with every new one
          if (violations.isNotEmpty()) reportReceivedViolations = true
          result.path
            ?.let { newPathFrom(startState, it, violationCondition) }
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

    if (!targetReached) {
      pathsPending = false
      return AnalysisResult(summaries, null)
    }
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
    recordInvariants: Boolean = true,
    probe: Boolean = false,
  ): RunResult {
    statistics.analyses++
    val extraction =
      extractBlockXcfa(
        sourceProcedure,
        block,
        precondition =
          (if (restriction == True()) start.state else And(start.state, restriction)).takeUnless {
            it == True()
          },
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
      // A probe's path may end in its may condition, so it says nothing about real error paths
      return RunResult.Unsafe(
        if (usesPathViolations && !probe) pathViolation(result.asUnsafe().cex, extraction) else null
      )
    }
    val proof = result.asSafe().proof
    // Witness invariants need a start state that covers the block's entries
    if (recordInvariants && restriction == True()) {
      invariantsByStart[start.state] =
        proof
          .getPartitions()
          .entries
          .mapNotNull { (clone, states) ->
            extraction.originalLocations[clone]?.let { it to states }
          }
          .groupBy({ it.first }, { it.second })
          .mapValues { (_, states) -> states.flatten().map { it.toExpr() }.distinct() }
    }
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

  /**
   * [found], or if its path is already known, a path from [start] outside all known ones (null if
   * there is none). A run yields one path, and its predecessors may refute every path sent so far,
   * so a known path must not hide the others; [pathsPending] makes the block look again.
   */
  private fun newPathFrom(
    start: Summary,
    found: PathViolation,
    violationCondition: Expr<BoolType>?,
  ): PathViolation? {
    if (found.condition !in pathViolationsSoFar) return found
    val exclusions =
      pathViolationsSoFar.map {
        checkNotNull(withoutAuxVars(it) { condition -> !operators.isUnsat(condition) }) {
          "Block ${block.id}: a path violation condition ties nondeterministic values to program " +
            "variables, so the known error paths cannot be excluded: $it"
        }
      }
    val outside = start.copy(state = And(start.state, Not(Or(exclusions))))
    val next =
      (run(outside, violationCondition, recordInvariants = false) as? RunResult.Unsafe)?.path
        ?: return null
    check(next.condition !in pathViolationsSoFar) {
      "Block ${block.id}: an excluded error path recurred: ${next.condition}"
    }
    return next
  }

  /** Predecessors keep only the last condition per sender, so refuted paths must stay in. */
  private fun accumulatePathViolations(new: Collection<Expr<BoolType>>): Expr<BoolType>? {
    val before = pathViolationsSoFar.size
    pathViolationsSoFar += new
    pathsPending = !block.isRoot && pathViolationsSoFar.size > before
    if (new.isEmpty()) return null
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
    if (summaries.isEmpty() && !trackSummaries) return emptyList()
    val unique = deduplicateStates(summaries)
    return listOf(
      DssPostConditionMessage(
        block.id,
        unique.map { it.state }.ifEmpty { listOf(False()) },
        unique.flatMapTo(linkedSetOf()) { it.precision },
        version = if (trackSummaries) ++postconditionVersion else 0,
        inputs = if (trackSummaries) inputVersions.toMap() else emptyMap(),
        restricted = restricted,
        // Successors keep the sender's older states instead, which still cover the exit
        observerOnly = unique.isEmpty(),
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
    statistics.violationConditionsSent++
    statistics.largestViolationCondition =
      maxOf(statistics.largestViolationCondition, ExprUtils.getAtoms(condition).size)
    return listOf(DssViolationConditionMessage(block.id, condition))
  }

  /** A query the solver cannot decide skips the generalization, never the analysis. */
  private fun generalizationOf(
    received: List<Pair<String, Expr<BoolType>>>
  ): ViolationGeneralizer.Generalization? {
    if (received.isEmpty()) return null
    return try {
      generalizer?.generalize(received, operators::isUnsat)
    } catch (e: DssUndecidedQueryException) {
      null
    }
  }

  override fun statistics(): Map<String, String> = statistics.toMap()

  override fun witness(): DssBlockWitness =
    DssBlockWitness(invariants(), violationRecords.toList(), reportedViolationConditions.toList())

  /** Invariants from start states that cover the block's real entries, else from top. */
  private fun invariants(): Map<XcfaLocation, List<Expr<BoolType>>>? {
    if (restricted) return null
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
