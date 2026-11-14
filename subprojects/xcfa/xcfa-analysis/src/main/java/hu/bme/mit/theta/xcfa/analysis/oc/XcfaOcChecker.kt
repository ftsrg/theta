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
import hu.bme.mit.theta.xcfa.utils.defaultValue
import java.util.IdentityHashMap
import kotlin.time.measureTime

private const val MAX_AUTO_CONFLICT_RFS = 5000

private const val ASSERTION_CHUNK_SIZE = 4096

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
    while (unbounded || bound <= forceUnrollBoundEnd) {
      logger.mainStep(
        "\nChecking with force loop unroll bound: $bound" +
          if (bounds.isEmpty()) "" else " (deepened: $bounds)"
      )
      val (result, reached) =
        Round(unroll(bound, bounds)).use { round ->
          val result = round.checkProperty()
          logger.mainStep("OC checker result: $result")
          if (!result.isSafe || !round.xcfa.unsafeUnrollUsed || acceptUnreliableSafe) {
            return result
          }
          if (maxExitQueries == 0) return@use result to null
          logger.mainStep("Incomplete loop unroll used: checking whether the bounds are reached...")
          result to round.reachedExits()
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
      val deepened =
        reached
          .filter { UnrollCut.of(it).deepenable }
          .associateWith { (bounds[it] ?: forceUnrollBoundStart) + forceUnrollBoundStep }
          .filterValues { unbounded || it <= forceUnrollBoundEnd }
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
      memoryModel.filter(eg.events, eg.pos, eg.wss).let { (ppos, wss) ->
        this.ppos = ppos
        this.wss = wss
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

    private fun checkProperty(checker: OcChecker<E>): SafetyResult<EmptyProof, Cex> {
      val races = races
      val targets = races?.map { it.condition } ?: eg.violations.map { it.guard }
      if (targets.isEmpty()) return SafetyResult.safe(EmptyProof.getInstance())

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
      races?.let { logger.info("Race candidates: ${it.size}") }

      logger.mainStep("Start checking...")
      val status: SolverStatus?
      val checkerTime = measureTime {
        // a violation has to be an execution, not only a model of the relaxed ordering constraints
        status =
          solve(checker, Or(targets)).let { if (it?.isSat == true) checker.distinctModel() else it }
      }
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

        status?.isSat == true -> {
          if (memoryModel == SC) {
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

        else -> SafetyResult.unknown()
      }
    }

    /**
     * The keys of the unroll exits some consistent execution reaches. Undecided exits count as
     * reached, which only costs an unnecessary deepening.
     */
    fun reachedExits(): Set<String> {
      val exitsByKey = eg.unrollExits.groupBy { it.key }
      val remaining = exitsByKey.keys.toMutableSet()
      val reached = mutableSetOf<String>()
      var queries = 0
      while (remaining.isNotEmpty()) {
        if (queries++ == maxExitQueries) {
          reached.addAll(remaining)
          break
        }
        val target = Or(remaining.flatMap { exitsByKey.getValue(it) }.map { it.guard })
        val found = query { checker ->
          val status: SolverStatus?
          val time = measureTime { status = solve(checker, target) }
          logger.info("Exit query $queries: $status in ${time.inWholeMilliseconds} ms")
          when {
            status?.isUnsat == true -> emptyList()
            status?.isSat == true -> {
              val model = GuardValues(checker.solver.model)
              remaining
                .filter { key -> exitsByKey.getValue(key).any { model.holds(it.guard) } }
                .ifEmpty { null }
            }
            else -> null // undecided
          }
        }
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
            } else if (parseContext.isGhostMemoryBase(rel.to.array)) {
              conseq = And(conseq, Eq(rel.to.const.ref, rel.to.const.type.defaultValue))
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
