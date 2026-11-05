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
package hu.bme.mit.theta.xcfa.analysis.dss.analysis

import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.solver.Interpolant
import hu.bme.mit.theta.solver.ItpPattern
import hu.bme.mit.theta.solver.ItpSolver
import hu.bme.mit.theta.solver.Solver
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.solver.SolverManager
import hu.bme.mit.theta.solver.SolverStatus
import hu.bme.mit.theta.solver.UCSolver

/** A block checker ran past the budget [DssDeadline] gave it; the next checker gets its turn. */
class DssBudgetExceededException(budgetMs: Long) :
  RuntimeException("DSS block analysis exceeded its budget of $budgetMs ms")

/** Whether [this] or one of its causes is a [DssBudgetExceededException]. */
fun Throwable.isDssBudgetExceeded(): Boolean =
  generateSequence(this) { it.cause }.any { it is DssBudgetExceededException }

/**
 * The deadline of the block analysis running on this thread. Theta's checkers cannot be
 * interrupted, but they spend their time in solver calls, so the solvers of [DeadlineSolverManager]
 * check the deadline before each call; a single call can still overrun it.
 */
object DssDeadline {

  private class Deadline(val budgetMs: Long, val endNanos: Long)

  private val current = ThreadLocal<Deadline?>()

  /** Runs [action] with [budgetMs] milliseconds (no limit for null), then restores the old one. */
  fun <T> within(budgetMs: Long?, action: () -> T): T {
    val outer = current.get()
    current.set(budgetMs?.let { Deadline(it, System.nanoTime() + it * 1_000_000) })
    try {
      return action()
    } finally {
      current.set(outer)
    }
  }

  fun check() {
    val deadline = current.get() ?: return
    if (System.nanoTime() > deadline.endNanos) throw DssBudgetExceededException(deadline.budgetMs)
  }
}

/** Solvers named `dss-deadline:<solver>`: `<solver>`'s, checking [DssDeadline] before each call. */
object DeadlineSolverManager : SolverManager() {

  const val PREFIX = "dss-deadline:"

  fun nameFor(solver: String) = PREFIX + solver

  /** [SolverManager.closeAll] unregisters every manager, so this runs before every DSS run. */
  fun ensureRegistered(solver: String) {
    try {
      resolveSolverFactory(nameFor(solver))
    } catch (e: UnsupportedOperationException) {
      if (e.message != "Solver ${nameFor(solver)} not supported") throw e
      registerSolverManager(this)
    }
  }

  override fun managesSolver(name: String): Boolean = name.startsWith(PREFIX)

  override fun getSolverFactory(name: String): SolverFactory =
    DeadlineSolverFactory(resolveSolverFactory(name.removePrefix(PREFIX)))

  override fun close() = Unit
}

class DeadlineSolverFactory(private val inner: SolverFactory) : SolverFactory {
  override fun createSolver(): Solver = DeadlineSolver(inner.createSolver())

  override fun createUCSolver(): UCSolver = DeadlineUCSolver(inner.createUCSolver())

  override fun createItpSolver(): ItpSolver = DeadlineItpSolver(inner.createItpSolver())
}

private class DeadlineSolver(private val inner: Solver) : Solver by inner {
  override fun check(): SolverStatus {
    DssDeadline.check()
    return inner.check()
  }

  override fun simplify(expr: Expr<BoolType>): Expr<BoolType> = inner.simplify(expr)
}

private class DeadlineUCSolver(private val inner: UCSolver) : UCSolver by inner {
  override fun check(): SolverStatus {
    DssDeadline.check()
    return inner.check()
  }

  override fun simplify(expr: Expr<BoolType>): Expr<BoolType> = inner.simplify(expr)
}

private class DeadlineItpSolver(private val inner: ItpSolver) : ItpSolver by inner {
  override fun check(): SolverStatus {
    DssDeadline.check()
    return inner.check()
  }

  override fun getInterpolant(pattern: ItpPattern): Interpolant {
    DssDeadline.check()
    return inner.getInterpolant(pattern)
  }

  override fun simplify(expr: Expr<BoolType>): Expr<BoolType> = inner.simplify(expr)
}
