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
import hu.bme.mit.theta.analysis.algorithm.oc.IDLOcChecker
import hu.bme.mit.theta.analysis.algorithm.oc.OcChecker
import hu.bme.mit.theta.analysis.unit.UnitPrec
import hu.bme.mit.theta.common.exception.NotSolvableException
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.booltype.BoolExprs.*
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.solver.Solver
import hu.bme.mit.theta.solver.SolverManager
import hu.bme.mit.theta.solver.SolverStatus
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.analysis.XcfaPrec
import hu.bme.mit.theta.xcfa.analysis.oc.XcfaOcMemoryConsistencyModel.SC
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.optimizeFurther
import hu.bme.mit.theta.xcfa.passes.AssumeFalseRemovalPass
import hu.bme.mit.theta.xcfa.passes.MutexToVarPass
import hu.bme.mit.theta.xcfa.passes.ProcedurePassManager
import hu.bme.mit.theta.xcfa.passes.UnrollExits
import hu.bme.mit.theta.xcfa.passes.UnrollPass
import kotlin.time.measureTime

/**
 * Bounded ordering-consistency checking with iterative deepening of the unroll bounds.
 *
 * Every round unrolls the loops (and recursive calls) the bound cannot resolve statically, routing
 * each cut-off continuation into an [unroll exit location][UnrollExits]. When the property query of
 * a round finds no violation, a second query asks which exits a consistent execution can reach: if
 * none, the unrolling covered every execution and the safe result is final. Otherwise only the cut
 * points found reachable are unrolled deeper in the next round; the others keep their bound but
 * stay exits, since deeper unrolling elsewhere can make them reachable again.
 *
 * With the IDL decision procedure under SC, data races are checked natively: a race is a pair of
 * conflicting accesses of different threads that can be at neighbouring clock values, i.e., with
 * nothing (in particular, no synchronisation) executed between them.
 */
class XcfaOcChecker(
  xcfa: XCFA,
  property: XcfaProperty,
  private val parseContext: ParseContext,
  private val decisionProcedure: OcDecisionProcedureType,
  private val smtSolver: String,
  private val logger: Logger,
  private val conflictInput: String?,
  private val outputConflictClauses: Boolean,
  private val nonPermissiveValidation: Boolean,
  autoConflictConfig: AutoConflictFinderConfig,
  autoConflictBound: Int,
  private val memoryModel: XcfaOcMemoryConsistencyModel = SC,
  private val acceptUnreliableSafe: Boolean = false,
  private val forceUnrollBoundStart: Int = 2,
  private val forceUnrollBoundEnd: Int = 2,
  private val forceUnrollBoundStep: Int = 1,
) : SafetyChecker<EmptyProof, Cex, XcfaPrec<UnitPrec>> {

  private val raceMode =
    property.verifiedProperty == ErrorDetection.DATA_RACE &&
      decisionProcedure == OcDecisionProcedureType.IDL &&
      memoryModel == SC

  init {
    check(property.verifiedProperty == ErrorDetection.ERROR_LOCATION || raceMode) {
      "Unsupported property by OC checker: $property. Consider using a specification " +
        "transformation (data races are supported natively by the IDL decision procedure under SC)."
    }
  }

  val xcfa =
    xcfa.optimizeFurther(
      ProcedurePassManager(listOf(AssumeFalseRemovalPass(property), MutexToVarPass()))
    )

  /** Cuts made before this checker (e.g. by the frontend) have no exit locations to query. */
  private val cutWithoutExits = this.xcfa.unsafeUnrollUsed

  private val conflictFinder = autoConflictConfig.conflictFinder(autoConflictBound)

  override fun check(prec: XcfaPrec<UnitPrec>?): SafetyResult<EmptyProof, Cex> {
    // A negative upper bound means "unbounded": keep deepening (BMC-style) until a reliable result
    // is found or resources run out.
    val unbounded = forceUnrollBoundEnd < 0
    require(forceUnrollBoundStep > 0) { "Force unroll bound step must be positive." }
    require(unbounded || forceUnrollBoundStart <= forceUnrollBoundEnd) {
      "Empty unroll bound range: $forceUnrollBoundStart..$forceUnrollBoundEnd"
    }
    // bounds of the cut points deepened so far; every other one is at forceUnrollBoundStart
    val bounds = mutableMapOf<String, Int>()
    while (true) {
      logger.mainStep(
        "\nChecking with force loop unroll bound: $forceUnrollBoundStart" +
          if (bounds.isEmpty()) "" else " (deepened: $bounds)"
      )
      val round = Round(unroll(bounds))
      val result = round.checkProperty()
      logger.mainStep("OC checker result: $result")
      if (!result.isSafe || !round.xcfa.unsafeUnrollUsed || acceptUnreliableSafe) {
        return result
      }

      logger.mainStep("Incomplete loop unroll used: checking whether the bounds are reached...")
      val reached = round.reachedExits()
      if (reached.isEmpty() && !cutWithoutExits) {
        logger.mainStep("No unroll bound is reached: the safe result is reliable.")
        return result
      }
      logger.mainStep("Unroll bounds reached at: $reached")
      val deepened =
        reached
          .filter { UnrollExits.kindOf(it).deepenable }
          .associateWith { (bounds[it] ?: forceUnrollBoundStart) + forceUnrollBoundStep }
          .filterValues { unbounded || it <= forceUnrollBoundEnd }
      if (deepened.isEmpty()) break
      bounds.putAll(deepened)
    }

    logger.mainStep(SafetyResult.unknown<EmptyProof, Cex>().toString())
    throw NotSolvableException()
  }

  /**
   * Force unrolls the XCFA for BMC. Re-running the pass per round is the point: each escalation
   * expands loops -- and recursive calls, which need parseContext for the parameter assignments --
   * one level deeper, which inlining, a one-shot pass, cannot do.
   */
  private fun unroll(bounds: Map<String, Int>): XCFA {
    val xcfa =
      xcfa.optimizeFurther(
        ProcedurePassManager(
          listOf(
            UnrollPass(
              forceUnrollBoundStart,
              parseContext = parseContext,
              specificRecursionUnrollLimit = forceUnrollBoundStart,
              cutBounds = bounds,
              markUnrollExits = true,
            )
          )
        )
      )
    logger.info("  -> unsafe unroll ${if (xcfa.unsafeUnrollUsed) "" else "NOT"} used")
    return xcfa
  }

  /** The queries on the event graph of one unrolling of the XCFA. */
  private inner class Round(val xcfa: XCFA) {

    private val eg: XcfaToEventGraph.EventGraph

    private val ppos: BooleanGlobalRelation

    private val wss: Map<VarDecl<*>, Set<R>>

    /** Constraints valid for every query on this event graph: known ordering conflicts. */
    private val lemmas = mutableListOf<Expr<BoolType>>()

    /**
     * The solver of all queries of the round when the decision procedure can share one: scoping
     * each query with push/pop keeps a round from leaving a solver (context) per query behind.
     */
    private val sharedSolver: Solver? =
      if (decisionProcedure.sharesSolver)
        SolverManager.resolveSolverFactory(smtSolver).createSolver()
      else null

    init {
      logger.mainStep("Creating event graph...")
      eg = XcfaToEventGraph(xcfa, parseContext, raceMode).create()
      memoryModel.filter(eg.events, eg.pos, eg.wss).let { (ppos, wss) ->
        this.ppos = ppos
        this.wss = wss
      }
    }

    private fun <T> query(block: (OcChecker<E>) -> T): T {
      sharedSolver?.push()
      val checker = decisionProcedure.checker(smtSolver, memoryModel, sharedSolver)
      try {
        return block(checker)
      } finally {
        if (sharedSolver != null) sharedSolver.pop() else checker.solver.close()
      }
    }

    fun checkProperty(): SafetyResult<EmptyProof, Cex> = query { checkProperty(it) }

    private fun checkProperty(ocChecker: OcChecker<E>): SafetyResult<EmptyProof, Cex> {
      val checker =
        if (conflictInput == null || raceMode) ocChecker
        else XcfaOcCorrectnessValidator(ocChecker, conflictInput, !nonPermissiveValidation, logger)
      val races = if (raceMode) raceCandidates(eg, ppos, checker as IDLOcChecker<E>) else null
      val targets = races?.map { it.condition } ?: eg.violations.map { it.guard }
      if (targets.isEmpty()) return SafetyResult.safe(EmptyProof.getInstance())

      logger.info(
        "Auto conflict time (ms): " +
          measureTime {
              val conflicts = conflictFinder.findConflicts(eg.events, ppos, eg.rfs, logger)
              lemmas.addAll(conflicts.map { Not(it.expr) })
              logger.info("Auto conflicts: ${conflicts.size}")
            }
            .inWholeMilliseconds
      )
      races?.let { logger.info("Race candidates: ${it.size}") }

      logger.mainStep("Start checking...")
      val status: SolverStatus?
      val checkerTime = measureTime { status = solve(checker, Or(targets)) }
      if (checker !is XcfaOcCorrectnessValidator)
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
          // theory lemmas of this event graph: they speed up the reachability query of the exits
          lemmas.addAll(checker.getPropagatedClauses().map { Not(it.expr) })
          SafetyResult.safe(EmptyProof.getInstance())
        }

        status?.isSat == true -> {
          if (checker is XcfaOcCorrectnessValidator)
            return SafetyResult.unsafe(EmptyCex.getInstance(), EmptyProof.getInstance())
          if (memoryModel == SC) {
            val trace =
              try {
                val extractor = XcfaOcTraceExtractor(xcfa, checker, eg)
                if (races == null) extractor.trace
                else {
                  val model = checker.solver.model
                  val race = races.first { it.condition.holdsIn(model) }
                  val (e1, e2) =
                    race.pairs.first { (e1, e2) -> race.pairCondition(e1, e2).holdsIn(model) }
                  logger.info("Data race: $e1 and $e2")
                  extractor.raceTrace(e1, e2)
                }
              } catch (e: Exception) {
                logger.info("OC checker trace extraction failed: ${e.message}")
                EmptyCex.getInstance()
              }
            SafetyResult.unsafe(trace, EmptyProof.getInstance())
          } else {
            SafetyResult.unsafe(EmptyCex.getInstance(), EmptyProof.getInstance())
          }
        }

        else -> SafetyResult.unknown()
      }
    }

    /**
     * The keys of the unroll exits that some consistent execution reaches. One model may reach
     * several exits, so this asks again for the ones not seen yet, until none is left or a bounded
     * number of queries; whatever is undecided then is assumed reachable, which only costs an
     * unnecessary deepening.
     */
    fun reachedExits(): Set<String> {
      val exitsByKey = eg.unrollExits.groupBy { it.key }
      val remaining = exitsByKey.keys.toMutableSet()
      val reached = mutableSetOf<String>()
      var queries = 0
      while (remaining.isNotEmpty()) {
        if (queries++ == MAX_EXIT_QUERIES) {
          reached.addAll(remaining)
          break
        }
        val target = Or(remaining.flatMap { exitsByKey.getValue(it) }.map { it.guard })
        // null: the query is undecided
        val found = query { checker ->
          val status: SolverStatus?
          val time = measureTime { status = solve(checker, target) }
          logger.info("Exit query $queries: $status in ${time.inWholeMilliseconds} ms")
          when {
            status?.isUnsat == true -> emptyList()
            status?.isSat == true -> {
              val model = checker.solver.model
              remaining
                .filter { key -> exitsByKey.getValue(key).any { it.guard.holdsIn(model) } }
                .ifEmpty { null } // the model should show one: do not trust it
            }
            else -> null
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

    private fun solve(checker: OcChecker<E>, target: Expr<BoolType>): SolverStatus? {
      logger.info("Adding constraints...")
      addToSolver(eg, checker.solver)
      lemmas.forEach { checker.solver.add(it) }
      checker.solver.add(target)
      return checker.check(eg.events, eg.pos, ppos, eg.rfs, wss)
    }
  }

  private fun Expr<BoolType>.holdsIn(model: Valuation): Boolean =
    try {
      (eval(model) as? BoolLitExpr)?.value == true
    } catch (_: Exception) {
      false
    }

  private fun addToSolver(eg: XcfaToEventGraph.EventGraph, solver: Solver) {
    // Value assignment
    eg.events.values
      .flatMap { it.values.flatten() }
      .filter { it.assignment != null }
      .forEach { event ->
        if (event.guard.isEmpty()) solver.add(event.assignment)
        else solver.add(Imply(event.guardExpr, event.assignment))
      }

    // Branching conditions
    eg.branchingConditions.forEach { solver.add(it) }

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
            }
            solver.add(Imply(rel.declRef, conseq)) // RF-Val
          }
          solver.add(Imply(event.guardExpr, Or(rels.map { it.declRef }))) // RF-Some
        }
    }
  }

  companion object {
    /** The global segment counter introduced by the witness instrumentation (ApplyWitnessPass). */
    private const val SEGMENT_COUNTER = "__THETA__segment__counter__"

    private const val MAX_EXIT_QUERIES = 8
  }
}
