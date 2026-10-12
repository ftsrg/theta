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

import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.False
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Not
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Or
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.solver.SolverManager
import hu.bme.mit.theta.xcfa.dss.analysis.CheckerFactory
import hu.bme.mit.theta.xcfa.dss.analysis.DssCheckerRoster
import hu.bme.mit.theta.xcfa.dss.analysis.DssPredicateOperators
import hu.bme.mit.theta.xcfa.dss.analysis.combinePredicatePrecisions
import hu.bme.mit.theta.xcfa.dss.analysis.computeViolationCondition
import hu.bme.mit.theta.xcfa.dss.analysis.extractBlockXcfa
import hu.bme.mit.theta.xcfa.dss.analysis.globalAssumePredicates
import hu.bme.mit.theta.xcfa.dss.analysis.packPostcondition
import hu.bme.mit.theta.xcfa.dss.analysis.predicatePrecision
import hu.bme.mit.theta.xcfa.dss.analysis.predicatesOf
import hu.bme.mit.theta.xcfa.dss.analysis.predicatesOfPrecision
import hu.bme.mit.theta.xcfa.dss.analysis.runWorkerConfig
import hu.bme.mit.theta.xcfa.dss.decomposition.Block
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import hu.bme.mit.theta.xcfa.model.XcfaProcedure

/**
 * The solver DSS uses by default: Theta's default (legacy) Z3 binding, whose native interpolation
 * handles the integer arithmetic of C programs. It must not be used by several threads at once (it
 * crashes natively in `solverAssert`, even with one context per block analysis), so the concurrent
 * executor needs `Z3:new` - whose Horn-based interpolation, however, fails on some C arithmetic.
 * See `doc/DSS.md`.
 */
const val DEFAULT_DSS_SOLVER = "Z3"

/**
 * The block analysis of DSS with predicate abstraction: a port of CPAchecker's `DssBlockAnalysis`
 * (driven the way CPAchecker's `DssAnalysisWorker.processMessage` drives it), on top of an ordinary
 * Theta checker that analyzes the block extracted into a standalone XCFA ([extractBlockXcfa]).
 *
 * The method names follow CPAchecker's:
 * - [runInitialAnalysis]: analyze the block from the most general entry state (top). If no target
 *   is reachable, broadcast the postcondition; otherwise remember that the block contains a
 *   violation, broadcast a top postcondition (if the block has successors) and a violation
 *   condition.
 * - On a postcondition message: [storePrecondition] (coverage check against what the sender sent
 *   before), then [analyzePrecondition] - which only re-analyzes if there is something to check (a
 *   violation inside the block or a violation condition from a successor), with only the new,
 *   relevant start states.
 * - On a violation-condition message: [storeViolationCondition] (drop unsatisfiable or repeated
 *   conditions), then [analyzeViolationCondition] - re-analyze from every stored precondition with
 *   the received condition as target. A refuted condition makes the checker refine, and the more
 *   precise postconditions are broadcast; a condition that is still reachable is propagated to the
 *   predecessors as a new violation condition (the weakest precondition through this block,
 *   [computeViolationCondition]). A violation condition of the root block means the program is
 *   unsafe (see [DssBlockActor]).
 *
 * Preconditions are kept per sender as a list of states, like CPAchecker's multimap: a new state
 * replaces the states of the same sender that it implies (a stronger, refined postcondition), and
 * is not relevant for re-analysis if an existing state of that sender implies it. Every start state
 * is analyzed separately. While some predecessor has not reported yet (or reported top), the top
 * state is analyzed too (`appendTopToRelevantIfNecessary`), so every intermediate result
 * over-approximates the reachable states. The handling of strongly connected components in the
 * paper ("prevent postconditions of predecessors in the same component from being joined unless
 * they are unequal to the initial state") is CPAchecker's: once every predecessor provided a
 * non-trivial state, top states that were themselves computed from non-trivial preconditions are
 * skipped. Only top states are skipped: Theta used to skip non-top states computed from top as
 * well, but that is unsound - such a state can be the only one that already carries entry states a
 * loop reaches in later iterations (`stateful_check`: the block after the loop only kept the states
 * of the first iteration and proved a reachable error unreachable). Without it, Cartesian
 * abstraction (and the global predicate pool) can produce coarse non-top summaries from top that
 * sustain themselves around a cycle of the block graph, so DSS may not terminate on such loops.
 *
 * Precision: like CPAchecker, the predicates a block used are transmitted with its postconditions,
 * and a block analyzes non-top start states with the combination of the precisions it received
 * (`combinePrecisionIfPossible`, unless [resetPrecisionForEveryRun]); top start states use the
 * start precision. Theta-specific: with [useGlobalPredicatePool], the start precision contains
 * every assume condition of the whole program (see `globalAssumePredicates`), which CPAchecker does
 * not have. Also Theta-specific: with [reuseBlockPrecision], every run additionally starts with the
 * predicates the block's earlier CEGAR runs ended with ([ownPrecision]); checkers that report no
 * precision (the bounded ones) neither add to nor use it. With [checkerFallback], a run whose
 * checker throws is repeated with the roster's next checkers (see `runWithCheckerFallback`).
 *
 * [checkerRoster] supplies the checker of every single analysis run (default: round-robin over the
 * configured checkers). [solverFactory] is used for the coverage and satisfiability checks of the
 * predicate operators; `null` resolves [DEFAULT_DSS_SOLVER].
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

    data object Unsafe : RunResult
  }

  private data class AnalysisResult(
    val summaries: List<Summary>,
    val violationCondition: Expr<BoolType>?,
  )

  private val operators by lazy {
    DssPredicateOperators(solverFactory ?: SolverManager.resolveSolverFactory(DEFAULT_DSS_SOLVER))
  }

  private val startPrecision: Set<Expr<BoolType>> by lazy {
    if (useGlobalPredicatePool) globalAssumePredicates(wholeProgram) else emptySet()
  }

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
      RunResult.Unsafe -> {
        containsViolationInsideBlock = true
        buildList {
          // CPAchecker sends the top state as postcondition if the block end is reachable at all;
          // a Theta checker stops at the first counterexample, so this uses "the block has
          // successors" as the (over-approximating) stand-in for "the block end was reached".
          if (block.successorIds.isNotEmpty()) {
            add(DssPostConditionMessage(block.id, listOf(True()), startPrecision))
          }
          addAll(reportViolationConditions(targetsOfOwnViolations()))
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
      return true
    }
    for (new in received) {
      var isRelevant = true
      for (old in stored.toList()) {
        if (operators.isSubsumed(new.state, old.state)) {
          stored.remove(old)
        }
        if (isRelevant && operators.isSubsumed(old.state, new.state)) {
          isRelevant = false
        }
      }
      if (isRelevant) relevant.add(new)
      stored.add(new)
    }
    if (relevant.isEmpty()) return false
    appendTopToRelevantIfNecessary(sender)
    return true
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
   * Stores the violation condition of [message]; returns whether the analysis should proceed: not
   * if the condition is unsatisfiable (CPAchecker's
   * `ProceedPredicateStateOperator.processBackward`) or if it is the same as the last one from the
   * same sender.
   */
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
   * Runs the block analysis with [violations] attached to the violation-condition location, from
   * the relevant start states ([checkOnlyRelevant], after a new precondition) or from all stored
   * preconditions (after a new violation condition).
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

    // CPAchecker leaves the order of the start states unspecified (hash order of its multimap).
    // Non-trivial states go first here: deduplication keeps the first of two states that cover
    // each other, and a top summary first would swallow every non-trivial summary of the same
    // analysis - then a loop block never sees a non-trivial precondition from itself, the SCC rule
    // above never applies, and its violation conditions are unrolled forever.
    val orderedStartStates = startStates.sortedBy { it.isTop }
    val violationCondition = if (violations.isEmpty()) null else or(violations)
    val summaries = mutableListOf<Summary>()
    var targetReached = false
    var reportReceivedViolations = false
    var analyzedTrivial = false
    for (start in orderedStartStates) {
      if (start.isTop && analyzedTrivial) continue
      analyzedTrivial = analyzedTrivial || start.isTop
      val precision =
        if (resetPrecisionForEveryRun || start.isTop) startPrecision
        else combinePrecisionIfPossible() ?: start.precision
      // A CPAchecker start state is an abstraction over the predicates of the precision it was sent
      // with, so its own predicates are always available to the analysis. Theta's transmitted
      // precision is only approximated (see predicatesOf), so the state's atoms are added
      // explicitly - otherwise the block-end abstraction can forget what the precondition said
      // (e.g. a loop counter's lower bound), and a loop block keeps re-deriving its violation
      // conditions from its own over-approximated postconditions forever.
      val startState = start.copy(precision = precision + predicatesOf(listOf(start.state)))

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
        RunResult.Unsafe -> {
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
          if (
            violations.isNotEmpty() &&
              (!checkOnlyRelevant ||
                startStates.size == 1 ||
                !start.isTop ||
                violationCondition !in reportedFromTop)
          ) {
            reportReceivedViolations = true
            if (start.isTop && violationCondition != null) reportedFromTop += violationCondition
          }
        }
      }
    }

    if (!targetReached) return AnalysisResult(summaries, null)
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
    return combinePredicatePrecisions(preconditions.values.flatten().map { it.precision }) +
      startPrecision
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
    val initialPrecision = initialPredicates.takeIf { it.isNotEmpty() }?.let(::predicatePrecision)
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
              if (reuseBlockPrecision)
                { precision -> ownPrecision += predicatesOfPrecision(precision) }
              else null,
          )
          .also { check(it.isSafe || it.isUnsafe) { "Inconclusive block analysis result: $it" } }
      }
    if (result.isUnsafe) return RunResult.Unsafe
    val proof = result.asSafe().proof
    val reached = proof.getPartitions().values.flatten().map { it.toExpr() }
    return RunResult.Safe(
      normalize(packPostcondition(result, extraction.exitLocation)),
      predicatesOf(reached) + start.precision,
    )
  }

  /**
   * Runs [analysis] with the roster's next checker. With [checkerFallback], an analysis whose
   * checker throws (a solver error, an unknown result, an unsupported operation, or an inconclusive
   * result, e.g. of a bounded checker) is repeated with the roster's following checkers (which ones
   * is up to the roster's selection strategy, see `DssCheckerSelectionStrategy`), at most once per
   * roster entry; if all of them throw, the first failure propagates with the others suppressed.
   * Errors (e.g. out of memory) and interruptions are never retried.
   */
  private inline fun <T> runWithCheckerFallback(
    trace: Array<Pair<String, Any?>> = emptyArray(),
    analysis: (CheckerFactory) -> T,
  ): T {
    val attempts = if (checkerFallback) checkerRoster.size else 1
    var failure: Exception? = null
    repeat(attempts) { attempt ->
      try {
        return DssTrace.span(
          "analysis",
          *trace,
          "attempt" to attempt,
          outcome = { result ->
            (result as? SafetyResult<*, *>)?.let { if (it.isSafe) "safe" else "unsafe" } ?: "ok"
          },
        ) {
          analysis(checkerRoster.next(attempt))
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
   * CPAchecker's abstraction formulas are canonical (BDD-based), so a valid abstraction is
   * literally `true`, which is what `isMostGeneralBlockEntryState` checks for. Theta's packed
   * states are disjunctions of predicate cubes, so validity is checked explicitly.
   */
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

  /** CPAchecker's `deduplicateStates`: drop every state covered by a state kept before it. */
  private fun deduplicateStates(summaries: List<Summary>): List<Summary> {
    if (summaries.size < 2) return summaries
    val kept = mutableListOf<Summary>()
    for (summary in summaries) {
      if (kept.none { operators.isSubsumed(summary.state, it.state) }) {
        kept += summary
      }
    }
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

  private fun or(exprs: List<Expr<BoolType>>): Expr<BoolType> =
    when (exprs.size) {
      0 -> False()
      1 -> exprs.single()
      else -> Or(exprs)
    }
}
