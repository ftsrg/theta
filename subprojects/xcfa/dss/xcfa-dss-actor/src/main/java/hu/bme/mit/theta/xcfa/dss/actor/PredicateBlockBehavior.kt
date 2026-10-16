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
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
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
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.analysis.reverseMapping
import hu.bme.mit.theta.xcfa.dss.analysis.BlockXcfaExtraction
import hu.bme.mit.theta.xcfa.dss.analysis.CheckerFactory
import hu.bme.mit.theta.xcfa.dss.analysis.DssAuxVars
import hu.bme.mit.theta.xcfa.dss.analysis.DssCheckerRoster
import hu.bme.mit.theta.xcfa.dss.analysis.DssPredicateOperators
import hu.bme.mit.theta.xcfa.dss.analysis.DssSolverStatistics
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

/**
 * The default DSS solver: legacy Z3. Its interpolation handles C integer arithmetic, but it crashes
 * when used by several threads, so the concurrent executor needs `Z3:new` (see `doc/DSS.md`).
 */
const val DEFAULT_DSS_SOLVER = "Z3"

/** MathSAT through JavaSMT: needs only the bundled native library, no SMT-LIB installation. */
const val DEFAULT_DSS_FALLBACK_SOLVER = "JavaSMT:MATHSAT5"

/**
 * DSS block analysis with predicate abstraction: a port of CPAchecker's `DssBlockAnalysis` over an
 * ordinary Theta checker on the extracted block ([extractBlockXcfa]), keeping CPAchecker's names.
 */
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
  private val fallbackSolverFactory: SolverFactory? = null,
  private val solverStatistics: DssSolverStatistics = DssSolverStatistics(),
) : DssBlockBehavior {

  /** CPAchecker's `StateAndPrecision`, plus the flag CPAchecker keeps in the `BlockState`. */
  private data class Summary(
    val state: Expr<BoolType>,
    val precision: Set<Expr<BoolType>>,
    val nonTrivialForEachPredecessor: Boolean = false,
  ) {
    /** CPAchecker's `isMostGeneralBlockEntryState` for predicate states. */
    val isTop: Boolean
      get() = state == True()
  }

  private sealed interface RunResult {
    data class Safe(val postcondition: Expr<BoolType>, val precision: Set<Expr<BoolType>>) :
      RunResult

    /** [path] is only computed for blocks with an internal cycle (see [pathViolation]). */
    data class Unsafe(val path: PathViolation?) : RunResult
  }

  /**
   * The violation condition of one counterexample, and whether it reached the received violation
   * condition (instead of one of the block's own targets).
   */
  private data class PathViolation(
    val condition: Expr<BoolType>,
    val reachedReceivedViolation: Boolean,
  )

  /** Theta-only: such blocks get violation conditions per counterexample path. */
  private val usesPathViolations: Boolean by lazy { hasInternalCycle(block) }

  /** Every path violation condition this block found so far, see [accumulatePathViolations]. */
  private val pathViolationsSoFar = linkedSetOf<Expr<BoolType>>()

  private data class AnalysisResult(
    val summaries: List<Summary>,
    val violationCondition: Expr<BoolType>?,
  )

  private val operators by lazy {
    DssPredicateOperators(
      solverFactory ?: SolverManager.resolveSolverFactory(DEFAULT_DSS_SOLVER),
      fallbackSolverFactory,
      solverStatistics,
    )
  }

  private val startPrecision: Set<Expr<BoolType>> by lazy {
    if (useGlobalPredicatePool) wholeProgram.collectAssumePreds() else emptySet()
  }

  /** The roster index of this block's fastest checker, if the roster ranks per block. */
  private var fastestChecker: Int? = null

  /** With [reuseBlockPrecision]: the predicates this block's CEGAR analyses ended with so far. */
  private val ownPrecision = linkedSetOf<Expr<BoolType>>()

  private val preconditions = LinkedHashMap<String, MutableList<Summary>>()
  private val violationConditions = LinkedHashMap<String, MutableList<Expr<BoolType>>>()
  private val relevant = mutableListOf<Summary>()
  private var containsViolationInsideBlock = false
  /** The received violation conditions a violation condition was reported for from top. */
  private val reportedFromTop = mutableSetOf<Expr<BoolType>>()

  /** The block's own error locations: targets of the specification, CPAchecker's target states. */
  private val ownTargets: List<XcfaLocation> = block.locations.filter { it.error }

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
          // CPAchecker sends the top state as postcondition if the block end is reachable at all;
          // a Theta checker stops at the first counterexample, so this uses "the block has
          // successors" as the (over-approximating) stand-in for "the block end was reached".
          if (block.successorIds.isNotEmpty()) {
            add(DssPostConditionMessage(block.id, listOf(True()), startPrecision))
          }
          addAll(
            result.path?.let {
              reportViolationCondition(accumulatePathViolations(listOf(it.condition)))
            } ?: reportViolationConditions(targetsOfOwnViolations())
          )
        }
      }
    }
  }

  /**
   * Stores the postconditions of [message] as preconditions of this block; returns whether the
   * analysis should proceed (CPAchecker's `DssMessageProcessing.shouldProceed`).
   */
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
      tracePrecondition(message, received.size, evicted = 0)
      return true
    }
    var evicted = 0
    for (new in received) {
      var isRelevant = true
      for (old in stored.toList()) {
        if (operators.isLeq(new.state, old.state)) {
          stored.remove(old)
          evicted++
        }
        if (isRelevant && operators.isLeq(old.state, new.state)) {
          isRelevant = false
        }
      }
      if (isRelevant) relevant.add(new)
      stored.add(new)
    }
    val newStates = relevant.size
    if (relevant.isNotEmpty()) appendTopToRelevantIfNecessary(sender)
    tracePrecondition(message, newStates, evicted)
    return relevant.isNotEmpty()
  }

  /** [newStates] of the message's states were not covered; the others were. */
  private fun tracePrecondition(message: DssPostConditionMessage, newStates: Int, evicted: Int) {
    if (!DssTrace.enabled) return
    DssTrace.event(
      "pc-in",
      "actor" to block.id,
      "from" to message.senderId,
      "states" to message.postconditions.size,
      "new" to newStates,
      "covered" to message.postconditions.size - newStates,
      "evicted" to evicted,
      "withTop" to (relevant.size > newStates),
      "prec" to message.precision.size,
      *traceContent(message.postcondition),
    )
  }

  private fun appendTopToRelevantIfNecessary(sender: String) {
    // calculate for all new states but do not under-approximate
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

  /**
   * Stores [message]'s violation condition; returns whether to proceed: not if it is unsatisfiable
   * (CPAchecker's `processBackward`) or repeats the sender's last one.
   */
  fun storeViolationCondition(message: DssViolationConditionMessage): Boolean {
    val condition =
      requireNotNull(message.violationCondition) { "Expected a violation condition in $message" }
    val sender = message.senderId
    val old = violationConditions.remove(sender).orEmpty().toSet()
    if (operators.isKnownUnsat(condition)) {
      traceViolationCondition(message, "unsat")
      return false
    }
    violationConditions[sender] = mutableListOf(condition)
    traceViolationCondition(message, if (condition in old) "repeated" else "new")
    return condition !in old
  }

  private fun traceViolationCondition(message: DssViolationConditionMessage, outcome: String) {
    if (!DssTrace.enabled) return
    DssTrace.event(
      "vc-in",
      "actor" to block.id,
      "from" to message.senderId,
      "outcome" to outcome,
      *traceContent(message.violationCondition),
    )
  }

  fun analyzePrecondition(): Collection<DssMessage> {
    if (!containsViolationInsideBlock && violationConditions.isEmpty()) {
      return emptyList()
    }
    val result =
      analyzeViolationCondition(violationConditions.values.flatten(), checkOnlyRelevant = true)
    return reportViolationCondition(result.violationCondition) +
      reportPostconditions(result.summaries)
  }

  fun analyzeViolationCondition(sender: String): Collection<DssMessage> {
    relevant.clear()
    val violations = violationConditions[sender]
    require(!violations.isNullOrEmpty()) { "No violation condition found for sender ID: $sender" }
    val result = analyzeViolationCondition(violations, checkOnlyRelevant = false)
    return reportPostconditions(result.summaries) +
      reportViolationCondition(result.violationCondition)
  }

  /**
   * Runs the block analysis with [violations] attached at the block exit, from the relevant start
   * states ([checkOnlyRelevant]) or from all stored preconditions.
   */
  private fun analyzeViolationCondition(
    violations: List<Expr<BoolType>>,
    checkOnlyRelevant: Boolean,
  ): AnalysisResult {
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
        // The paper's SCC rule, as in CPAchecker: skip only *top* states computed from non-trivial
        // preconditions. Skipping non-top states computed from top too is unsound (stateful_check).
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

    // Non-trivial start states go first (CPAchecker leaves the order unspecified): deduplication
    // keeps the first of two covering states, and a top summary first would swallow the others,
    // so a loop block's SCC rule would never apply and its violation conditions unroll forever.
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
      // Add the start state's own atoms to its precision: Theta's transmitted precision is only
      // approximate, and without them the block-end abstraction can forget the precondition, so a
      // loop block re-derives its violation conditions forever.
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
          // CPAchecker's block analysis keeps exploring after a target and still yields the
          // block-end states; a Theta checker stops at the counterexample, so the postcondition is
          // computed by a second run without targets.
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
          // CPAchecker: "For trivial states, the same vc must have been sent already." That does
          // not hold if the violation condition arrived while this block had no precondition yet
          // (then it was not analyzed at all), so here it is checked instead of assumed.
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
            ?.let { pathViolations += it.condition }
        }
      }
    }

    if (!targetReached) return AnalysisResult(summaries, null)
    if (usesPathViolations) {
      val condition = accumulatePathViolations(pathViolations)
      return AnalysisResult(summaries, condition)
    }
    // Theta's checker does not tell which target its counterexample reached, so the violation
    // condition covers every target CPAchecker would collect paths to after a violation: the
    // block's own targets (if it contains a violation) and the received violation conditions.
    val targets = buildMap {
      if (containsViolationInsideBlock) putAll(targetsOfOwnViolations())
      if (reportReceivedViolations && violationCondition != null) {
        put(block.violationConditionLocation, violationCondition)
      }
    }
    val newViolationCondition =
      targets.takeIf { it.isNotEmpty() }?.let { computeViolationCondition(block, it) }
    return AnalysisResult(summaries, newViolationCondition)
  }

  private fun targetsOfOwnViolations(): Map<XcfaLocation, Expr<BoolType>> =
    ownTargets.associateWith { True() }

  private fun combinePrecisionIfPossible(): Set<Expr<BoolType>>? {
    if (preconditions.isEmpty()) return null
    return combinePredPrecs(preconditions.values.flatten().map { it.precision }) + startPrecision
  }

  /** One analysis of the block with an ordinary Theta checker. */
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
    val trace =
      arrayOf<Pair<String, Any?>>(
        "block" to block.id,
        "preds" to initialPredicates.size,
        "pre" to !start.isTop,
        "vc" to (violationCondition != null),
      )
    val result =
      runWithCheckerFallback(trace) { checker ->
        runWorkerConfig(
            extraction.xcfa,
            checker,
            initialPrecision,
            onLastPrec =
              if (reuseBlockPrecision) { precision -> ownPrecision += precision.collectPreds() }
              else null,
          )
          .also { check(it.isSafe || it.isUnsafe) { "Inconclusive block analysis result: $it" } }
      }
    if (result.isUnsafe) {
      return RunResult.Unsafe(
        if (usesPathViolations) pathViolation(result.asUnsafe().cex, extraction) else null
      )
    }
    val proof = result.asSafe().proof
    val reached = proof.getPartitions().values.flatten().map { it.toExpr() }
    return RunResult.Safe(
      normalize(packPostcondition(result, extraction.exitLocation)),
      reached.collectPreds() + start.precision,
    )
  }

  /**
   * The violation condition of [cex]'s path after the precondition edge, with CEGAR's per-process
   * variable copies renamed back; conditions over other variables are rejected.
   */
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
    // CEGAR traces start with a Nop self loop at the initial location, before the precondition edge
    val path = actions.drop(actions.indexOfFirst { it.isOn(extraction.preconditionEdge) } + 1)
    val condition = computePathViolationCondition(path.map { it.label.changeVars(originalOf) })
    val unknown =
      ExprUtils.getVars(condition).filterNot { it in programVars || DssAuxVars.isAux(it) }
    check(unknown.isEmpty()) {
      "Block ${block.id}: path violation condition over unknown variables $unknown: $condition"
    }
    return PathViolation(condition, actions.last().isOn(extraction.violationConditionEdge))
  }

  /**
   * The disjunction of [new] and all earlier path violation conditions: predecessors keep only each
   * sender's last condition, so the growing union keeps refuted paths from recurring.
   */
  private fun accumulatePathViolations(new: Collection<Expr<BoolType>>): Expr<BoolType>? {
    if (new.isEmpty()) return null
    val before = pathViolationsSoFar.size
    pathViolationsSoFar += new
    DssTrace.event(
      "path-vcs",
      "actor" to block.id,
      "found" to new.size,
      "added" to pathViolationsSoFar.size - before,
      "total" to pathViolationsSoFar.size,
    )
    return Or(pathViolationsSoFar)
  }

  private val programVars: Set<VarDecl<*>> by lazy {
    sourceProcedure.vars + wholeProgram.globalVars.map { it.wrappedVar }
  }

  /**
   * Runs [analysis] with the roster's next checker. With [checkerFallback], failures are retried on
   * the following checkers, once each (never errors or interrupts); see also [runEveryChecker].
   */
  private inline fun <T> runWithCheckerFallback(
    trace: Array<Pair<String, Any?>> = emptyArray(),
    analysis: (CheckerFactory) -> T,
  ): T {
    val leader = fastestChecker
    if (checkerRoster.ranksPerBlock && leader == null) return runEveryChecker(trace, analysis)
    val order = leader?.let { listOf(it) + (0 until checkerRoster.size).filter { i -> i != it } }
    val attempts = order?.size ?: if (checkerFallback) checkerRoster.size else 1
    var failure: Exception? = null
    repeat(attempts) { attempt ->
      val index = order?.get(attempt)
      try {
        return traceAnalysis(trace, attempt, index) {
          analysis(if (index != null) checkerRoster[index] else checkerRoster.next(attempt))
        }
      } catch (e: InterruptedException) {
        throw e
      } catch (e: Exception) {
        failure?.addSuppressed(e) ?: run { failure = e }
      }
    }
    throw checkNotNull(failure)
  }

  /**
   * Runs [analysis] with every checker and returns the fastest one's result, which sets
   * [fastestChecker]. If all throw, the first failure propagates and the next analysis retries all.
   */
  private inline fun <T> runEveryChecker(
    trace: Array<Pair<String, Any?>>,
    analysis: (CheckerFactory) -> T,
  ): T {
    var failure: Exception? = null
    var fastest = -1
    var fastestNanos = Long.MAX_VALUE
    var fastestResult: T? = null
    val millis = arrayOfNulls<Long>(checkerRoster.size)
    repeat(checkerRoster.size) { index ->
      val start = System.nanoTime()
      try {
        val result = traceAnalysis(trace, index, index) { analysis(checkerRoster[index]) }
        val nanos = System.nanoTime() - start
        millis[index] = nanos / 1_000_000
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
    DssTrace.event(
      "fastest-checker",
      "actor" to block.id,
      "checker" to fastest,
      "ms" to millis.joinToString(",") { it?.toString() ?: "failed" },
    )
    @Suppress("UNCHECKED_CAST") return fastestResult as T
  }

  /** One try of an analysis; [checker] is the roster index, if the roster ranks per block. */
  private inline fun <T> traceAnalysis(
    trace: Array<Pair<String, Any?>>,
    attempt: Int,
    checker: Int?,
    analysis: () -> T,
  ): T =
    DssTrace.span(
      "analysis",
      *trace,
      "attempt" to attempt,
      *(if (checker != null) arrayOf("checker" to checker) else emptyArray()),
      outcome = { result ->
        (result as? SafetyResult<*, *>)?.let { if (it.isSafe) "safe" else "unsafe" } ?: "ok"
      },
      action = analysis,
    )

  /**
   * Normalizes [state], detecting validity explicitly: CPAchecker's BDD abstractions are literally
   * `true` when valid, while Theta's packed states are disjunctions of predicate cubes.
   */
  private fun normalize(state: Expr<BoolType>): Expr<BoolType> {
    val simplified = ExprUtils.simplify(state)
    return if (simplified != False() && operators.isKnownUnsat(Not(simplified))) True()
    else simplified
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

  /** CPAchecker's `deduplicateStates`: drop every state covered by a state kept before it. */
  private fun deduplicateStates(summaries: List<Summary>): List<Summary> {
    if (summaries.size < 2) return summaries
    val kept = mutableListOf<Summary>()
    for (summary in summaries) {
      if (kept.none { operators.isLeq(summary.state, it.state) }) {
        kept += summary
      }
    }
    DssTrace.event("pc-dedup", "actor" to block.id, "states" to summaries.size, "kept" to kept.size)
    return kept
  }

  private fun reportViolationConditions(
    targets: Map<XcfaLocation, Expr<BoolType>>
  ): Collection<DssMessage> = reportViolationCondition(computeViolationCondition(block, targets))

  private fun reportViolationCondition(condition: Expr<BoolType>?): Collection<DssMessage> {
    if (condition == null || condition == False()) return emptyList()
    // PredicateViolationConditionOperator: the root block only reports satisfiable conditions,
    // since its violation condition decides the verdict.
    if (block.isRoot && operators.isUnsat(condition)) return emptyList()
    return listOf(DssViolationConditionMessage(block.id, condition))
  }
}
