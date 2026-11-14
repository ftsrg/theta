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
package hu.bme.mit.theta.xcfa.analysis.oc

import hu.bme.mit.theta.analysis.Cex
import hu.bme.mit.theta.analysis.EmptyCex
import hu.bme.mit.theta.analysis.algorithm.EmptyProof
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.algorithm.oc.BooleanGlobalRelation
import hu.bme.mit.theta.analysis.algorithm.oc.Event
import hu.bme.mit.theta.analysis.algorithm.oc.EventType
import hu.bme.mit.theta.analysis.algorithm.oc.OcChecker
import hu.bme.mit.theta.analysis.unit.UnitPrec
import hu.bme.mit.theta.common.exception.NotSolvableException
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.booltype.AndExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.*
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.NotExpr
import hu.bme.mit.theta.core.type.booltype.OrExpr
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.solver.AssumingSolver
import hu.bme.mit.theta.solver.InterruptibleSolver
import hu.bme.mit.theta.solver.Solver
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.solver.SolverStatus
import hu.bme.mit.theta.xcfa.ErrorDetection.DATA_RACE
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.analysis.XcfaPrec
import hu.bme.mit.theta.xcfa.analysis.oc.XcfaOcMemoryConsistencyModel.SC
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.optimizeFurther
import hu.bme.mit.theta.xcfa.passes.*
import hu.bme.mit.theta.xcfa.passes.concurrency.MutexToVarPass
import hu.bme.mit.theta.xcfa.passes.loops.SpinLoopEffectPass
import hu.bme.mit.theta.xcfa.passes.loops.UnrollCut
import hu.bme.mit.theta.xcfa.passes.loops.UnrollPass
import hu.bme.mit.theta.xcfa.passes.memory.ReferenceElimination
import hu.bme.mit.theta.xcfa.passes.structure.AssumeFalseRemovalPass
import java.util.IdentityHashMap
import java.util.concurrent.Executors
import java.util.concurrent.ScheduledExecutorService
import java.util.concurrent.TimeUnit
import kotlin.time.Duration
import kotlin.time.Duration.Companion.seconds
import kotlin.time.measureTime

private const val MAX_AUTO_CONFLICT_RFS = 5000

private const val ASSERTION_CHUNK_SIZE = 4096

/**
 * The least time an exit query of a round gets once the round has found an exit to deepen. Such a
 * query only decides which other cuts to deepen now: a stopped one is asked again in the next
 * round.
 */
private val MIN_EXIT_QUERY_BUDGET = 30.seconds

private val budgetTimer: ScheduledExecutorService by lazy {
  Executors.newSingleThreadScheduledExecutor {
    Thread(it, "oc-exit-query-budget").apply { isDaemon = true }
  }
}

/**
 * Bounded OC checking; IDL under SC checks data races natively. With [maxExitQueries] != 0 (< 0: no
 * limit), only the cut points whose [unroll exits][UnrollCut] are reachable are unrolled deeper.
 */
class XcfaOcChecker(
  private val xcfa: XCFA,
  private val property: XcfaProperty,
  private val parseContext: ParseContext,
  private val decisionProcedure: OcDecisionProcedureType,
  private val solverFactory: SolverFactory,
  private val logger: Logger,
  private val outputConflictClauses: Boolean,
  autoConflictConfig: AutoConflictFinderConfig,
  autoConflictBound: Int,
  private val memoryModel: XcfaOcMemoryConsistencyModel = SC,
  private val acceptUnreliableSafe: Boolean = false,
  private val forceUnrollBoundStart: Int = 2,
  private val forceUnrollBoundEnd: Int = 2,
  private val forceUnrollBoundStep: Int = 1,
  private val maxExitQueries: Int = -1,
) : SafetyChecker<EmptyProof, Cex, XcfaPrec<UnitPrec>> {

  init {
    check(decisionProcedure.supportsProperty(property.verifiedProperty, memoryModel)) {
      "Unsupported property by OC checker: $property. Consider using a specification" +
        "transformation."
    }
  }

  // cuts made before this checker (e.g. by the frontend) have no exit locations to query
  private val cutWithoutExits = xcfa.unsafeUnrollUsed

  private val conflictFinder = autoConflictConfig.conflictFinder(autoConflictBound)

  /**
   * Whether a round that is deepened anyway may skip the proof of the property: its first exit
   * query then also asks for a violation, so a round without reached exits still decides it.
   */
  private val deferProofs = decisionProcedure == OcDecisionProcedureType.IDL && maxExitQueries != 0

  /**
   * The property is still checked on its own in exponentially spaced rounds, to find violations.
   */
  private fun isProofRound(round: Int) =
    round <= 2 || (Integer.bitCount(round) == 1 && Integer.numberOfTrailingZeros(round) % 2 == 1)

  override fun check(prec: XcfaPrec<UnitPrec>?): SafetyResult<EmptyProof, Cex> {
    // A negative upper bound means "unbounded": keep deepening the force-unroll bound (BMC-style)
    // until a reliable result is found or resources run out.
    val unbounded = forceUnrollBoundEnd < 0
    require(forceUnrollBoundStep > 0) { "Force unroll bound step must be positive." }
    require(unbounded || forceUnrollBoundStart <= forceUnrollBoundEnd) {
      "Empty unroll bound range: $forceUnrollBoundStart..$forceUnrollBoundEnd"
    }
    var bound = forceUnrollBoundStart
    val bounds = mutableMapOf<String, Int>()
    fun deepened(reached: Set<String>) =
      reached
        .filter { UnrollCut.of(it).deepenable }
        .associateWith { (bounds[it] ?: forceUnrollBoundStart) + forceUnrollBoundStep }
        .filterValues { unbounded || it <= forceUnrollBoundEnd }
    fun deepenable(key: String) = deepened(setOf(key)).isNotEmpty()
    var rounds = 0
    while (unbounded || bound <= forceUnrollBoundEnd) {
      logger.mainStep(
        "\nChecking with force loop unroll bound: $bound" +
          if (bounds.isEmpty()) "" else " (deepened: $bounds)"
      )
      rounds++
      val (result, reached) =
        Round(unroll(bound, bounds)).use { round ->
          val deferred =
            deferProofs &&
              !isProofRound(rounds) &&
              round.xcfa.unsafeUnrollUsed &&
              !acceptUnreliableSafe
          val early = if (deferred) round.reachedExits(::deepenable, withViolation = true) else null
          round.violation?.let {
            logger.mainStep("OC checker result: $it")
            return it
          }
          // without a deeper round to follow, this round has to decide the property itself
          if (early != null && (round.propertyProved || deepened(early).isNotEmpty())) {
            return@use SafetyResult.safe<EmptyProof, Cex>(EmptyProof.getInstance()) to early
          }
          val result = round.checkProperty()
          if (!result.isSafe || !round.xcfa.unsafeUnrollUsed || acceptUnreliableSafe) {
            logger.mainStep("OC checker result: $result")
            return result
          }
          // not a verdict yet, so not logged in the form that readers of the output take for one
          logger.mainStep("No violation within the unroll bounds.")
          if (maxExitQueries == 0) return@use result to null
          logger.mainStep("Incomplete loop unroll used: checking whether the bounds are reached...")
          result to (early ?: round.reachedExits(::deepenable))
        }
      if (reached == null) {
        logger.mainStep("Incomplete loop unroll bound ($bound) used: safe result is unreliable.")
        bound += forceUnrollBoundStep
        continue
      }
      if (reached.isEmpty() && !cutWithoutExits) {
        logger.mainStep("No unroll bound is reached: the safe result is reliable.")
        return result
      }
      logger.mainStep("Unroll bounds reached at: $reached")
      val deepened = deepened(reached)
      if (deepened.isEmpty()) break
      bounds.putAll(deepened)
    }

    logger.mainStep(SafetyResult.unknown<EmptyProof, Cex>().toString())
    throw NotSolvableException()
  }

  private fun unroll(bound: Int, bounds: Map<String, Int>): XCFA {
    // Force loop unroll for BMC. Re-running the pass per bound is the point: each escalation
    // expands loops -- and recursive calls, which need parseContext for the parameter assignments
    // -- one level deeper, which inlining, a one-shot pass, cannot do.
    val xcfa =
      xcfa.optimizeFurther(
        ProcedurePassManager(
          listOf(
            SpinLoopEffectPass(property),
            UnrollPass(
              bound,
              parseContext = parseContext,
              specificRecursionUnrollLimit = bound,
              cutBounds = bounds,
              markUnrollExits = maxExitQueries != 0,
            ),
            // recursive calls are spliced in only now, and their arguments can be computed
            // addresses
            ReferenceElimination(parseContext),
            AssumeFalseRemovalPass(property),
            MutexToVarPass(),
          )
        )
      )
    logger.info("  -> unsafe unroll ${if (xcfa.unsafeUnrollUsed) "" else "NOT"} used")
    return xcfa
  }

  /** The queries on the event graph of one unrolling of the XCFA. */
  private inner class Round(val xcfa: XCFA) : AutoCloseable {

    private val eg: XcfaToEventGraph.EventGraph

    private val ppos: BooleanGlobalRelation

    private val wss: Map<VarDecl<*>, Set<R>>

    /** Ordering conflicts of this event graph, valid for every query of the round. */
    private val lemmas = linkedSetOf<Expr<BoolType>>()

    private val checker = decisionProcedure.checker(solverFactory, memoryModel)

    init {
      logger.mainStep("Creating event graph...")
      eg =
        XcfaToEventGraph(
            xcfa,
            parseContext,
            property.verifiedProperty,
            memoryModel == SC,
            // the Z3 propagator crashes if its first check is an exit query under a solver scope
            decisionProcedure != OcDecisionProcedureType.PROPAGATOR,
          )
          .create()
      logger.info(
        "Event graph: ${eg.events.values.sumOf { it.values.sumOf { e -> e.size } }} events," +
          " ${eg.rfs.values.sumOf { it.size }} read-from candidates," +
          " ${eg.violations.size} violations"
      )
      memoryModel.filter(eg.events, eg.pos, eg.wss).let { (ppos, wss) ->
        this.ppos = ppos
        this.wss = wss
      }
      logStatistics()
    }

    private fun logStatistics() {
      val events = eg.events.mapValues { it.value.values.flatten() }
      val memory = events.filterKeys { it in eg.memoryDecls }.values.flatten()
      val all = events.values.flatten()
      fun counts(es: List<E>) =
        "${es.count { it.type == EventType.READ }} reads, ${es.count { it.type == EventType.WRITE }} writes"
      logger.info(
        "Event graph: ${counts(all)} of ${events.size} variables (memory: ${counts(memory)}); " +
          "${eg.rfs.values.sumOf { it.size }} read-from and ${wss.values.sumOf { it.size }} " +
          "write-order candidates; ${Event.clkSize} clocks; ${eg.unrollExits.size} unroll exits"
      )
      eg.rfs.entries
        .sortedByDescending { it.value.size }
        .take(4)
        .forEach { (v, rfs) ->
          logger.info("  ${v.name}: ${counts(events[v].orEmpty())}, ${rfs.size} read-from")
        }
    }

    override fun close() {
      checker.solver.close()
    }

    /** Declares every clock the encoding has to cover, so it comes before [encoded]. */
    private val races by lazy {
      if (property.verifiedProperty == DATA_RACE) raceCandidates(eg, ppos, checker) else null
    }

    /** Below the scope of the queries: they differ in their targets only, and share the rest. */
    private val encoded by lazy {
      races
      checker.prepare(eg.events, eg.pos, ppos, eg.rfs, wss).also {
        if (it) addToSolver(eg, checker.solver)
      }
    }

    private fun <T> query(block: (OcChecker<E>) -> T): T {
      // learned clauses outlive an assumption, but not a solver scope
      if (encoded && checker.solver is AssumingSolver) return block(checker)
      checker.solver.push()
      try {
        return block(checker)
      } finally {
        checker.solver.pop()
      }
    }

    fun checkProperty(): SafetyResult<EmptyProof, Cex> = query { checkProperty(it) }

    /** The conditions under which the property is violated. */
    private val targets by lazy { races?.map { it.condition } ?: eg.violations.map { it.guard } }

    private val autoConflicts by lazy {
      logger.info(
        "Auto conflict time (ms): " +
          measureTime {
              // the lemmas are redundant hints, and the search is quadratic in the read-from
              // candidates
              val conflicts =
                if (eg.rfs.values.sumOf { it.size } > MAX_AUTO_CONFLICT_RFS) listOf()
                else conflictFinder.findConflicts(eg.events, ppos, eg.rfs, logger)
              lemmas.addAll(conflicts.map { Not(it.expr) })
              logger.info("Auto conflicts: ${conflicts.size}")
            }
            .inWholeMilliseconds
      )
    }

    /** Set by [reachedExits] when its first query was also for a violation, and found one. */
    var violation: SafetyResult<EmptyProof, Cex>? = null
      private set

    /** Whether [reachedExits] refuted a violation together with the exits. */
    var propertyProved = false
      private set

    private fun checkProperty(checker: OcChecker<E>): SafetyResult<EmptyProof, Cex> {
      val races = races
      if (targets.isEmpty()) return SafetyResult.safe(EmptyProof.getInstance())

      autoConflicts
      races?.let { logger.info("Race candidates: ${it.size}") }

      logger.mainStep("Start checking...")
      val status: SolverStatus?
      val checkerTime = measureTime {
        // a violation has to be an execution, not only a model of the relaxed ordering constraints
        status =
          solve(checker, Or(targets)).let { if (it?.isSat == true) checker.distinctModel() else it }
      }
      solvingTime += checkerTime
      logger.info("Solver time (ms): ${checkerTime.inWholeMilliseconds}")
      logger.info("Propagated clauses: ${checker.getPropagatedClauses().size}")
      checker.solver.statistics.let {
        logger.info("Solver statistics:")
        it.forEach { (k, v) -> logger.info("$k: $v") }
      }

      return when {
        status?.isUnsat == true -> {
          if (outputConflictClauses)
            System.err.println(
              "Conflict clause output time (ms): ${
                measureTime {
                  checker.getPropagatedClauses().forEach { System.err.println("CC: $it") }
                }.inWholeMilliseconds
              }"
            )
          lemmas.addAll(checker.getPropagatedClauses().map { Not(it.expr) })
          SafetyResult.safe(EmptyProof.getInstance())
        }

        status?.isSat == true -> unsafeResult(checker)

        else -> SafetyResult.unknown()
      }
    }

    private fun unsafeResult(checker: OcChecker<E>): SafetyResult<EmptyProof, Cex> {
      val races = races
      return if (memoryModel == SC) {
        val race = races?.let { racingPair(checker, it) }
        val trace =
          try {
            val extractor = XcfaOcTraceExtractor(xcfa, checker, eg)
            if (races == null) extractor.trace
            else {
              val (e1, e2) = race ?: error("No racing pair holds in the model.")
              extractor.raceTrace(e1, e2)
            }
          } catch (e: Exception) {
            logger.info("OC checker trace extraction failed: ${e.message}")
            if (race != null) RaceOnlyCex() else EmptyCex.getInstance()
          }
        race?.let { (e1, e2) -> XcfaOcDataRaces.record(trace, e1, e2) }
        SafetyResult.unsafe(trace, EmptyProof.getInstance())
      } else {
        SafetyResult.unsafe(EmptyCex.getInstance(), EmptyProof.getInstance())
      }
    }

    /**
     * The keys of the unroll exits some consistent execution reaches. Undecided exits count as
     * reached, which only costs an unnecessary deepening. Once an exit is found that will be
     * deepened, a query that takes longer than the round so far is stopped, and the exits it asked
     * for count as not reached: the next round asks for them again.
     */
    fun reachedExits(deepenable: (String) -> Boolean, withViolation: Boolean = false): Set<String> {
      val exitsByKey = eg.unrollExits.groupBy { it.key }
      val remaining = exitsByKey.keys.toMutableSet()
      val reached = mutableSetOf<String>()
      var queries = 0
      // only the first query is also for a violation: later ones leave the property undecided
      var violations = if (withViolation) targets else listOf()
      if (withViolation && violations.isEmpty()) propertyProved = true
      while (remaining.isNotEmpty() || violations.isNotEmpty()) {
        if (queries++ == maxExitQueries) {
          reached.addAll(remaining)
          break
        }
        val asked = violations
        violations = listOf()
        val target = Or(asked + remaining.flatMap { exitsByKey.getValue(it) }.map { it.guard })
        val budget =
          if (reached.any(deepenable)) maxOf(MIN_EXIT_QUERY_BUDGET, solvingTime) else null
        val found = query { checker ->
          if (asked.isNotEmpty()) autoConflicts
          var status: SolverStatus? = null
          val time = measureTime {
            status = withinBudget(budget) { solve(checker, target) }
            // a violation has to be an execution, not only a model of the relaxed constraints
            if (status?.isSat == true && GuardValues(checker.solver.model).holdsAny(asked)) {
              status = checker.distinctModel()
            }
          }
          solvingTime += time
          if (interrupted) {
            logger.info("Exit query $queries: stopped after ${time.inWholeMilliseconds} ms")
            return@query emptyList()
          }
          logger.info("Exit query $queries: $status in ${time.inWholeMilliseconds} ms")
          when {
            status?.isUnsat == true -> {
              if (asked.isNotEmpty()) propertyProved = true
              emptyList()
            }
            status?.isSat == true -> {
              val model = GuardValues(checker.solver.model)
              if (model.holdsAny(asked)) {
                violation = unsafeResult(checker)
                return@query emptyList()
              }
              remaining
                .filter { key -> exitsByKey.getValue(key).any { model.holds(it.guard) } }
                .ifEmpty { null }
            }
            else -> null // undecided
          }
        }
        if (violation != null) return emptySet()
        if (found == null) {
          reached.addAll(remaining)
          break
        }
        if (found.isEmpty()) break
        reached.addAll(found)
        remaining.removeAll(found.toSet())
      }
      return reached
    }

    private var queryCount = 0

    /** The time the queries of this round took so far. */
    private var solvingTime = Duration.ZERO

    /** Whether a budget stopped a check, after which the solver of the round checks no more. */
    private var interrupted = false

    /** The result of [check], or null if it ran out of [budget] and was stopped. */
    private fun <T> withinBudget(budget: Duration?, check: () -> T): T? {
      val solver = checker.solver as? InterruptibleSolver
      if (budget == null || solver == null) return check()
      val lock = Any()
      var running = true
      val timer =
        budgetTimer.schedule(
          {
            synchronized(lock) {
              if (running) {
                interrupted = true
                solver.interrupt()
              }
            }
          },
          budget.inWholeMilliseconds,
          TimeUnit.MILLISECONDS,
        )
      try {
        val result = runCatching(check)
        synchronized(lock) { running = false }
        return if (interrupted) null else result.getOrThrow()
      } finally {
        timer.cancel(false)
      }
    }

    private fun solve(checker: OcChecker<E>, target: Expr<BoolType>): SolverStatus? {
      logger.info("Adding constraints...")
      if (!encoded) addToSolver(eg, checker.solver)
      lemmas.forEach { checker.solver.add(it) }
      if (encoded && checker.solver is AssumingSolver) {
        lemmas.clear()
        val query = Decls.Const("__theta_oc_query_${queryCount++}", Bool())
        checker.solver.add(Imply(query.ref, target))
        checker.assumption = query.ref
      } else {
        checker.solver.add(target)
      }
      return checker.check(eg.events, eg.pos, ppos, eg.rfs, wss)
    }
  }

  /** The conflicting accesses of a race candidate whose clocks are adjacent in the model. */
  private fun racingPair(checker: OcChecker<E>, races: List<RaceCandidate>): Pair<E, E>? =
    runCatching {
        val model = GuardValues(checker.solver.model)
        val race = races.first { model.holds(it.condition) }
        race.pairs.first { (e1, e2) -> model.holds(race.pairCondition(e1, e2)) }
      }
      .getOrNull()

  /** Guards share their subterms, so evaluating them as trees takes exponential time. */
  private class GuardValues(private val model: Valuation) {
    private val values = IdentityHashMap<Expr<BoolType>, Boolean>()

    fun holdsAny(guards: List<Expr<BoolType>>): Boolean = guards.any { holds(it) }

    fun holds(guard: Expr<BoolType>): Boolean =
      try {
        value(guard)
      } catch (_: Exception) {
        false
      }

    private fun value(expr: Expr<BoolType>): Boolean =
      values[expr]
        ?: when (expr) {
          is AndExpr -> expr.ops.all { value(it) }
          is OrExpr -> expr.ops.any { value(it) }
          is NotExpr -> !value(expr.op)
          else -> (expr.eval(model) as BoolLitExpr).value
        }.also { values[expr] = it }
  }

  /**
   * Asserts constraints in chunks: a solver call per constraint dominates on large event graphs.
   */
  private class Assertions(private val solver: Solver) {
    private val pending = mutableListOf<Expr<BoolType>>()

    fun add(expr: Expr<BoolType>) {
      pending.add(expr)
      if (pending.size >= ASSERTION_CHUNK_SIZE) flush()
    }

    fun flush() {
      if (pending.isEmpty()) return
      solver.add(if (pending.size == 1) pending.first() else And(pending.toList()))
      pending.clear()
    }
  }

  private fun addToSolver(eg: XcfaToEventGraph.EventGraph, target: Solver) {
    val solver = Assertions(target)
    // Value assignment
    eg.events.values
      .flatMap { it.values.flatten() }
      .filter { it.assignment != null }
      .forEach { event ->
        if (event.guard.isEmpty()) solver.add(event.assignment!!)
        else solver.add(Imply(event.guardExpr, event.assignment))
      }

    // Branching conditions
    eg.branchingConditions.forEach { solver.add(it) }

    // Local data flow
    eg.localFlows.forEach { solver.add(it) }

    // RF
    eg.rfs.forEach { (v, list) ->
      list
        .groupBy { it.to }
        .forEach { (event, rels) ->
          rels.forEach { rel ->
            var conseq = And(rel.from.guardExpr, rel.to.guardExpr)
            if (rel.from.const !in eg.memoryGarbages) {
              conseq = And(conseq, Eq(rel.from.const.ref, rel.to.const.ref))
              if (v in eg.memoryDecls) {
                conseq =
                  And(conseq, Eq(rel.from.array, rel.to.array), Eq(rel.from.offset, rel.to.offset))
              }
            } else {
              parseContext.getGhostMemoryInitialValue(rel.to.array)?.let {
                conseq = And(conseq, Eq(rel.to.const.ref, it))
              }
            }
            solver.add(Imply(rel.declRef, conseq)) // RF-Val
          }
          // A local may be unassigned on the path taken (e.g. the skipped call of `f() || g()`), so
          // a read must take its value from a write only if one of its candidates executed.
          // A candidate whose guard is a subset of the read's always executes with it.
          val mustRead =
            if (rels.any { event.guard.containsAll(it.from.guard) }) event.guardExpr
            else And(event.guardExpr, Or(rels.map { it.from.guardExpr }))
          solver.add(Imply(mustRead, Or(rels.map { it.declRef }))) // RF-Some
        }
    }
    solver.flush()
  }
}
