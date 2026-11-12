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

import hu.bme.mit.theta.xcfa.analysis.dss.decomposition.BlockGraph
import java.util.concurrent.atomic.AtomicInteger

/** Shared by all blocks of a run, so it must be thread-safe; state is keyed by list index. */
interface DssCheckerSelectionStrategy {

  fun select(checkers: List<CheckerFactory>): CheckerFactory

  fun select(checkers: List<CheckerFactory>, attempt: Int): CheckerFactory = select(checkers)

  /** Whether each block ranks the checkers itself (see [FastestCheckerSelectionStrategy]). */
  val ranksPerBlock: Boolean
    get() = false

  /** The checkers of one block, which [select] then picks from (see [finishingBlocks]). */
  fun checkersOf(checkers: List<CheckerFactory>, finishing: Boolean): List<CheckerFactory> =
    checkers
}

class RoundRobinCheckerSelectionStrategy : DssCheckerSelectionStrategy {

  private val cursor = AtomicInteger(0)

  override fun select(checkers: List<CheckerFactory>): CheckerFactory {
    // mod, not rem: stays non-negative after the counter overflows
    val index = cursor.getAndIncrement().mod(checkers.size)
    return checkers[index]
  }
}

class PriorityCheckerSelectionStrategy : DssCheckerSelectionStrategy {

  override fun select(checkers: List<CheckerFactory>): CheckerFactory = checkers.first()

  override fun select(checkers: List<CheckerFactory>, attempt: Int): CheckerFactory =
    checkers[attempt.coerceIn(0, checkers.size - 1)]
}

/** A block's first analysis runs every checker; the fastest leads its later analyses. */
class FastestCheckerSelectionStrategy :
  DssCheckerSelectionStrategy by PriorityCheckerSelectionStrategy() {

  override val ranksPerBlock: Boolean
    get() = true
}

/**
 * The last checker is a finisher, used first on the [finishingBlocks] only, as its postconditions
 * may be too coarse to build on. The other blocks use the others by priority.
 */
class FinisherCheckerSelectionStrategy :
  DssCheckerSelectionStrategy by PriorityCheckerSelectionStrategy() {

  override fun checkersOf(
    checkers: List<CheckerFactory>,
    finishing: Boolean,
  ): List<CheckerFactory> {
    require(checkers.size >= 2) { "A finisher needs another checker for the other blocks" }
    val others = checkers.dropLast(1)
    return if (finishing) listOf(checkers.last()) + others else others
  }
}

/**
 * The blocks without successors, whose postconditions no other block builds on (backward: the
 * program's first blocks).
 */
fun BlockGraph.finishingBlocks(): Set<String> =
  blocks.filter { it.successorIds.isEmpty() }.mapTo(linkedSetOf()) { it.id }

/**
 * The block checkers of a run, handed out by [strategy]. With a positive [budgetMs], each checker
 * gets that many milliseconds in turn, growing by [BUDGET_GROWTH] per round; the checkers must then
 * use [DeadlineSolverManager] solvers, which enforce it.
 */
class DssCheckerRoster(
  private val checkers: List<CheckerFactory>,
  private val strategy: DssCheckerSelectionStrategy = PriorityCheckerSelectionStrategy(),
  val budgetMs: Long = 0,
) {

  init {
    require(checkers.isNotEmpty()) { "DSS needs at least one checker to run blocks with" }
    require(budgetMs >= 0) { "A DSS checker budget cannot be negative: $budgetMs" }
  }

  /** Whether block analyses take turns with growing budgets (see the class documentation). */
  val budgeted: Boolean
    get() = budgetMs > 0 && checkers.size > 1 && !strategy.ranksPerBlock

  val size: Int
    get() = checkers.size

  val ranksPerBlock: Boolean
    get() = strategy.ranksPerBlock

  operator fun get(index: Int): CheckerFactory = checkers[index]

  /** The roster of one block (see [DssCheckerSelectionStrategy.checkersOf]). */
  fun forBlock(finishing: Boolean): DssCheckerRoster =
    DssCheckerRoster(strategy.checkersOf(checkers, finishing), strategy, budgetMs)

  fun next(attempt: Int = 0): CheckerFactory {
    val selected = strategy.select(checkers, attempt)
    require(selected in checkers) {
      "DssCheckerSelectionStrategy.select returned a checker not present in this roster"
    }
    return selected
  }

  companion object {
    const val BUDGET_GROWTH = 4L
  }
}
