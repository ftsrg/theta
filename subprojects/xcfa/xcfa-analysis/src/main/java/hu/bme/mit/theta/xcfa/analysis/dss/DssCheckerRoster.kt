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
package hu.bme.mit.theta.xcfa.analysis.dss

import java.util.concurrent.atomic.AtomicInteger

/** Shared by all blocks of a run, so it must be thread-safe; state is keyed by list index. */
interface DssCheckerSelectionStrategy {

  fun select(checkers: List<CheckerFactory>): CheckerFactory

  fun select(checkers: List<CheckerFactory>, attempt: Int): CheckerFactory = select(checkers)

  /** Whether each block ranks the checkers itself (see [FastestCheckerSelectionStrategy]). */
  val ranksPerBlock: Boolean
    get() = false
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

/** The block checkers of a run, handed out by [strategy]; one instance shared by all blocks. */
class DssCheckerRoster(
  private val checkers: List<CheckerFactory>,
  private val strategy: DssCheckerSelectionStrategy = RoundRobinCheckerSelectionStrategy(),
) {

  init {
    require(checkers.isNotEmpty()) { "DSS needs at least one checker to run blocks with" }
  }

  val size: Int
    get() = checkers.size

  val ranksPerBlock: Boolean
    get() = strategy.ranksPerBlock

  operator fun get(index: Int): CheckerFactory = checkers[index]

  fun next(attempt: Int = 0): CheckerFactory {
    val selected = strategy.select(checkers, attempt)
    require(selected in checkers) {
      "DssCheckerSelectionStrategy.select returned a checker not present in this roster"
    }
    return selected
  }
}
