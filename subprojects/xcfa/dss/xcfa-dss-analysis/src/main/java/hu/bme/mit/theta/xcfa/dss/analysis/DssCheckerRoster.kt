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

import java.util.concurrent.atomic.AtomicInteger

/**
 * Picks which [CheckerFactory] a [DssCheckerRoster] hands out next. One instance is shared across a
 * run, possibly from many threads; key any state by list index (lambdas lack structural equality).
 */
interface DssCheckerSelectionStrategy {

  fun select(checkers: List<CheckerFactory>): CheckerFactory

  /**
   * Chooses the checker for the [attempt]th try of one analysis (0 = first; later tries only under
   * `--dss-checker-fallback`). Defaults to plain [select].
   */
  fun select(checkers: List<CheckerFactory>, attempt: Int): CheckerFactory = select(checkers)

  /**
   * Whether each block ranks the checkers itself: its first analysis runs every checker, and the
   * fastest one leads its later analyses (see [FastestCheckerSelectionStrategy]).
   */
  val ranksPerBlock: Boolean
    get() = false
}

/**
 * Default strategy: cycles through [checkers] so each is used equally often (within one). A class,
 * not an object, so its cursor doesn't leak across runs; thread-safe via [AtomicInteger].
 */
class RoundRobinCheckerSelectionStrategy : DssCheckerSelectionStrategy {

  private val cursor = AtomicInteger(0)

  override fun select(checkers: List<CheckerFactory>): CheckerFactory {
    // .mod(), not %/.rem(): always non-negative for a positive divisor, so this stays correct even
    // after getAndIncrement() wraps Int around at ~2^31 calls (.rem() would go negative there and
    // throw on the list index below instead of just resuming the cycle).
    val index = cursor.getAndIncrement().mod(checkers.size)
    return checkers[index]
  }
}

/**
 * Fixed priority: every analysis runs `checkers[0]` first, and the [attempt]th try takes
 * `checkers[attempt]` (only under `--dss-checker-fallback`). Stateless, so it can be shared.
 */
class PriorityCheckerSelectionStrategy : DssCheckerSelectionStrategy {

  override fun select(checkers: List<CheckerFactory>): CheckerFactory = checkers.first()

  override fun select(checkers: List<CheckerFactory>, attempt: Int): CheckerFactory =
    checkers[attempt.coerceIn(0, checkers.size - 1)]
}

/**
 * Per-block fastest: a block's first analysis runs every checker, and the fastest leads its later
 * analyses, the rest as fallbacks ([ranksPerBlock]); else like [PriorityCheckerSelectionStrategy].
 */
class FastestCheckerSelectionStrategy :
  DssCheckerSelectionStrategy by PriorityCheckerSelectionStrategy() {

  override val ranksPerBlock: Boolean
    get() = true
}

/**
 * Equivalent [CheckerFactory]s, one handed out by [strategy] per [next] call (mixing different
 * analyses may never quiesce). Build once per run and share across blocks, or balancing breaks.
 */
class DssCheckerRoster(
  private val checkers: List<CheckerFactory>,
  private val strategy: DssCheckerSelectionStrategy = RoundRobinCheckerSelectionStrategy(),
) {

  init {
    require(checkers.isNotEmpty()) { "DSS needs at least one checker to run blocks with" }
  }

  /** The number of checkers in the roster (repeated entries counted separately). */
  val size: Int
    get() = checkers.size

  /** See [DssCheckerSelectionStrategy.ranksPerBlock]. */
  val ranksPerBlock: Boolean
    get() = strategy.ranksPerBlock

  /** The [index]th checker of the roster, for strategies that rank per block. */
  operator fun get(index: Int): CheckerFactory = checkers[index]

  /** The checker for the [attempt]th try of one analysis (see [DssCheckerSelectionStrategy]). */
  fun next(attempt: Int = 0): CheckerFactory {
    val selected = strategy.select(checkers, attempt)
    require(selected in checkers) {
      "DssCheckerSelectionStrategy.select returned a checker not present in this roster"
    }
    return selected
  }
}
