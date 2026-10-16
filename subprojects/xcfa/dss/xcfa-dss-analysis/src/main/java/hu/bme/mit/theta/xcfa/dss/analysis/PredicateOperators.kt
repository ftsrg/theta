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
package hu.bme.mit.theta.xcfa.dss.analysis

import hu.bme.mit.theta.analysis.pred.PredPrec
import hu.bme.mit.theta.analysis.ptr.PtrPrec
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolExprs.False
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Not
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.PathUtils
import hu.bme.mit.theta.solver.Solver
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.xcfa.analysis.XcfaPrec
import java.util.concurrent.atomic.AtomicInteger

/**
 * Solver-backed operators of CPAchecker's distributed predicate CPA ([isUnsat], [isKnownUnsat],
 * [isSubsumed]). Failed queries go to the fallback solver, then [DssUndecidedQueryException].
 */
class DssPredicateOperators(
  solverFactory: SolverFactory,
  fallbackSolverFactory: SolverFactory? = null,
  private val statistics: DssSolverStatistics = DssSolverStatistics(),
) {

  private val solver = OperatorSolver(solverFactory)
  private val fallbackSolver = fallbackSolverFactory?.let(::OperatorSolver)

  /**
   * Throws [DssUndecidedQueryException] if neither the solver nor the fallback solver decides
   * [expr]: here an undecided query must not be taken as satisfiable.
   */
  fun isUnsat(expr: Expr<BoolType>): Boolean =
    decide(expr) { failure -> throw DssUndecidedQueryException(failure) }

  /**
   * [isUnsat], but `false` if the fallback solver cannot decide [expr] either. Only for callers
   * where a missed unsat result merely skips a pruning or simplification step.
   */
  fun isKnownUnsat(expr: Expr<BoolType>): Boolean = decide(expr) { false }

  /** Whether state 1 implies state 2 per [isKnownUnsat]. */
  fun isSubsumed(state1: Expr<BoolType>, state2: Expr<BoolType>): Boolean =
    state2 == True() || state1 == state2 || isKnownUnsat(And(state1, Not(state2)))

  /** Without a fallback solver, a failure of the solver is never [undecided] but an exception. */
  private inline fun decide(expr: Expr<BoolType>, undecided: (Exception) -> Boolean): Boolean {
    if (expr == False()) return true
    if (expr == True()) return false
    statistics.queries.incrementAndGet()
    val failure =
      try {
        return solver.isUnsat(expr)
      } catch (e: Exception) {
        e
      }
    statistics.solverFailed.incrementAndGet()
    val fallback =
      fallbackSolver ?: throw DssUndecidedQueryException(failure).also { statistics.report() }
    return try {
      fallback.isUnsat(expr).also {
        statistics.fallbackDecided.incrementAndGet()
        statistics.report()
      }
    } catch (e: Exception) {
      statistics.fallbackFailed.incrementAndGet()
      statistics.report()
      e.addSuppressed(failure)
      undecided(e)
    }
  }
}

/**
 * Solver statistics shared by all blocks: [solverFailed] of [queries] went to the fallback solver,
 * which decided [fallbackDecided]; [checkerFailed]/[checkerFallbackDecided] likewise for checkers.
 */
class DssSolverStatistics(private val onSolverFailure: (DssSolverStatistics) -> Unit = {}) {
  val queries = AtomicInteger()
  val solverFailed = AtomicInteger()
  val fallbackDecided = AtomicInteger()
  val fallbackFailed = AtomicInteger()
  val checkerFailed = AtomicInteger()
  val checkerFallbackDecided = AtomicInteger()
  val checkerFallbackFailed = AtomicInteger()

  /** Called after every failure of the solver, so a run killed later still logged its counts. */
  fun report() = onSolverFailure(this)

  override fun toString() =
    "queries=$queries solverFailed=$solverFailed fallbackDecided=$fallbackDecided " +
      "fallbackFailed=$fallbackFailed checkerFailed=$checkerFailed " +
      "checkerFallbackDecided=$checkerFallbackDecided checkerFallbackFailed=$checkerFallbackFailed"
}

/**
 * A coverage or satisfiability query of [DssPredicateOperators] that the solver (and its fallback,
 * if any) failed on: an unknown result or a crash. DSS reports an unknown verdict for it.
 */
class DssUndecidedQueryException(cause: Throwable) :
  RuntimeException("DSS solver query undecided: $cause", cause)

/** One solver of [DssPredicateOperators]; a solver that threw is replaced by a fresh one. */
private class OperatorSolver(private val factory: SolverFactory) {

  private var solver: Solver? = null

  fun isUnsat(expr: Expr<BoolType>): Boolean {
    val current =
      solver ?: withSolverConstructionLock { factory.createSolver() }.also { solver = it }
    try {
      current.push()
      try {
        current.add(PathUtils.unfold(expr, 0))
        return current.check().isUnsat
      } finally {
        current.pop()
      }
    } catch (e: Exception) {
      solver = null
      runCatching { current.close() }
      throw e
    }
  }
}

/**
 * The predicates a block transmits as its precision: the atoms of a safe result's reached states
 * (Theta's checkers don't return their precision), without [DssAuxVars] variables.
 */
fun predicatesOf(exprs: Iterable<Expr<BoolType>>): Set<Expr<BoolType>> =
  exprs
    .flatMap(ExprUtils::getAtoms)
    .filter { it != True() && it != False() }
    .filter { atom -> ExprUtils.getVars(atom).none(DssAuxVars::isAux) }
    .toSet()

/**
 * CPAchecker's `CombinePredicatePrecisionOperator`: the union of [precisions], restricted to
 * predicates over variables common to all of them, if there are any.
 */
fun combinePredicatePrecisions(precisions: Collection<Set<Expr<BoolType>>>): Set<Expr<BoolType>> {
  if (precisions.isEmpty()) return emptySet()
  if (precisions.size == 1) return precisions.single()
  val count = HashMap<Any, Int>()
  for (precision in precisions) {
    for (variable in ExprUtils.getVars(precision)) count.merge(variable, 1, Int::plus)
  }
  val inAll = count.filterValues { it == precisions.size }.keys
  val important = inAll.ifEmpty { count.keys }
  return precisions
    .flatten()
    .filter { predicate -> ExprUtils.getVars(predicate).any { it in important } }
    .toSet()
}

/**
 * The predicates of a predicate-abstraction precision ([predicatePrecision]'s shape), filtered like
 * [predicatesOf]; empty for any other precision.
 */
fun predicatesOfPrecision(precision: XcfaPrec<*>): Set<Expr<BoolType>> =
  ((precision.p as? PtrPrec<*>)?.innerPrec as? PredPrec)?.preds?.let(::predicatesOf) ?: emptySet()

/** The initial precision a predicate-abstraction checker is started with for [predicates]. */
fun predicatePrecision(predicates: Set<Expr<BoolType>>): XcfaPrec<PtrPrec<PredPrec>> =
  XcfaPrec(PtrPrec(PredPrec.of(predicates), emptySet()))
