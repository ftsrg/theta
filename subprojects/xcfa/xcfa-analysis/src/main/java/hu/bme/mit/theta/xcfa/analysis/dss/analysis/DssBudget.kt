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
import hu.bme.mit.theta.solver.SolverBase
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.solver.SolverManager
import hu.bme.mit.theta.solver.SolverStatus
import hu.bme.mit.theta.solver.UCSolver
import java.util.concurrent.ScheduledThreadPoolExecutor
import java.util.concurrent.TimeUnit

/** A block checker ran past the budget [DssDeadline] gave it; the next checker gets its turn. */
class DssBudgetExceededException(budgetMs: Long, cause: Throwable? = null) :
  RuntimeException("DSS block analysis exceeded its budget of $budgetMs ms", cause)

/** Whether [this] or one of its causes is a [DssBudgetExceededException]. */
fun Throwable.isDssBudgetExceeded(): Boolean =
  generateSequence(this) { it.cause }.any { it is DssBudgetExceededException }

/**
 * The deadline of the block analysis running on this thread. Theta's checkers cannot be
 * interrupted, but they spend their time in solver calls: the solvers of [DeadlineSolverManager]
 * refuse to start a call once the deadline has passed, and a watchdog interrupts
 * ([SolverBase.interrupt]) the calls still running when it passes.
 *
 * An interrupted call may surface as any solver or checker failure, so every exception that leaves
 * an expired deadline counts as an overrun, not as a failure of the checker.
 */
object DssDeadline {

  private class Deadline(val budgetMs: Long) {
    private val endNanos = System.nanoTime() + budgetMs * 1_000_000
    private val running = mutableListOf<SolverBase>()
    private var ended = false

    val isOver: Boolean
      @Synchronized get() = ended || System.nanoTime() - endNanos > 0

    /** Interrupting under the lock keeps [leave], and so the solver's closing, from overlapping. */
    @Synchronized
    fun end() {
      ended = true
      running.forEach { it.interrupt() }
    }

    @Synchronized
    fun enter(solver: SolverBase) {
      if (isOver) throw DssBudgetExceededException(budgetMs)
      running.add(solver)
    }

    @Synchronized
    fun leave(solver: SolverBase) {
      running.remove(solver)
    }
  }

  private val watchdog =
    ScheduledThreadPoolExecutor(1) { task ->
        Thread(task, "dss-deadline-watchdog").apply { isDaemon = true }
      }
      .apply { removeOnCancelPolicy = true }

  private val current = ThreadLocal<Deadline?>()

  /** Runs [action] with [budgetMs] milliseconds (no limit for null), then restores the old one. */
  fun <T> within(budgetMs: Long?, action: () -> T): T {
    val outer = current.get()
    val deadline = budgetMs?.let(::Deadline)
    val watch = deadline?.let { watchdog.schedule(it::end, it.budgetMs, TimeUnit.MILLISECONDS) }
    current.set(deadline)
    try {
      return action()
    } catch (e: Exception) {
      throw if (deadline != null) overrunOrSelf(deadline, e) else e
    } finally {
      watch?.cancel(false)
      current.set(outer)
    }
  }

  fun check() {
    val deadline = current.get() ?: return
    if (deadline.isOver) throw DssBudgetExceededException(deadline.budgetMs)
  }

  /**
   * Runs [query] on [solver]; the watchdog interrupts [solver] if the deadline passes meanwhile.
   */
  internal fun <T> query(solver: SolverBase, query: () -> T): T {
    val deadline = current.get() ?: return query()
    deadline.enter(solver)
    try {
      return query()
    } catch (e: Exception) {
      throw overrunOrSelf(deadline, e)
    } finally {
      deadline.leave(solver)
    }
  }

  private fun overrunOrSelf(deadline: Deadline, e: Exception): Exception =
    if (deadline.isOver && e !is InterruptedException && !e.isDssBudgetExceeded())
      DssBudgetExceededException(deadline.budgetMs, e)
    else e
}

/** Solvers named `dss-deadline:<solver>`: `<solver>`'s, with every query under [DssDeadline]. */
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
  override fun check(): SolverStatus = DssDeadline.query(inner) { inner.check() }

  override fun simplify(expr: Expr<BoolType>): Expr<BoolType> = inner.simplify(expr)

  override fun interrupt() = inner.interrupt()
}

private class DeadlineUCSolver(private val inner: UCSolver) : UCSolver by inner {
  override fun check(): SolverStatus = DssDeadline.query(inner) { inner.check() }

  override fun simplify(expr: Expr<BoolType>): Expr<BoolType> = inner.simplify(expr)

  override fun interrupt() = inner.interrupt()
}

private class DeadlineItpSolver(private val inner: ItpSolver) : ItpSolver by inner {
  override fun check(): SolverStatus = DssDeadline.query(inner) { inner.check() }

  override fun getInterpolant(pattern: ItpPattern): Interpolant =
    DssDeadline.query(inner) { inner.getInterpolant(pattern) }

  override fun simplify(expr: Expr<BoolType>): Expr<BoolType> = inner.simplify(expr)

  override fun interrupt() = inner.interrupt()
}
