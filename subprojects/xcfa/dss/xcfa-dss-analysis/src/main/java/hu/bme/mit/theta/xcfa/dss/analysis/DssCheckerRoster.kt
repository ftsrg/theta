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
 * Chooses which [CheckerFactory] a [DssCheckerRoster] hands out next, given the full list it was
 * built from. Implementations that need to track usage across calls (e.g. round-robin's own cursor,
 * or a future "least-used" strategy's per-factory counts) own that state themselves, keyed by
 * **list index**, not by the [CheckerFactory] value - a `(XCFA) -> XcfaChecker` lambda has no
 * structural `equals`/`hashCode`, only referential identity, so indexing by value is a landmine a
 * future strategy could otherwise walk into.
 *
 * A single strategy instance is meant to be shared across an entire DSS run (see
 * [DssCheckerRoster]'s own doc for why) - implementations should not assume they're only ever
 * called from one thread.
 */
interface DssCheckerSelectionStrategy {

  fun select(checkers: List<CheckerFactory>): CheckerFactory

  /**
   * Chooses the checker for the [attempt]th try of one analysis (0 = first try; later tries happen
   * only under `--dss-checker-fallback`, after the previous checker failed). By default, every try
   * is just another [select] call.
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
 * The default [DssCheckerSelectionStrategy]: cycles through [checkers] in order, so - across
 * however many times [select] gets called in total - every checker in the list gets used the same
 * number of times, or as close to it as an uneven total allows (counts differ by at most one).
 *
 * Deliberately a `class`, not a stateless `object` singleton the way this codebase's other built-in
 * strategies are (e.g. `LoopCheckerSearchStrategy`'s `GDFS`/`NDFS`/`FULL`): round-robin needs its
 * own cursor to advance, and a process-wide singleton would leak that cursor's position across
 * unrelated DSS runs (and tests) sharing the same JVM. Construct a fresh instance per run instead -
 * exactly what [DssCheckerRoster]'s own default parameter already does.
 *
 * Thread-safe: DSS's concurrent executor calls [select] from every block's own thread, potentially
 * at the same instant. [AtomicInteger.getAndIncrement] is wait-free and linearizable, so every call
 * gets a distinct, gap-free counter value regardless of interleaving - the round-robin balance
 * guarantee above holds *exactly*, not just approximately, no matter how calls actually race in
 * practice.
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
 * A fixed-priority [DssCheckerSelectionStrategy]: every analysis first runs with `checkers[0]`; the
 * following entries are used only as fallbacks, in list order (the [attempt]th try takes
 * `checkers[attempt]`). Without `--dss-checker-fallback`, only the first checker is ever used.
 * Stateless, so one instance can be shared freely.
 */
class PriorityCheckerSelectionStrategy : DssCheckerSelectionStrategy {

  override fun select(checkers: List<CheckerFactory>): CheckerFactory = checkers.first()

  override fun select(checkers: List<CheckerFactory>, attempt: Int): CheckerFactory =
    checkers[attempt.coerceIn(0, checkers.size - 1)]
}

/**
 * Per-block fastest checker: a block's first analysis runs with every checker in list order, and
 * the one that finished it fastest leads every later analysis of that block, followed by the others
 * as fallbacks in list order (with or without `--dss-checker-fallback`). The ranking is state of
 * each block analysis, which [ranksPerBlock] tells to keep it; outside of that, the order is
 * [PriorityCheckerSelectionStrategy]'s.
 */
class FastestCheckerSelectionStrategy :
  DssCheckerSelectionStrategy by PriorityCheckerSelectionStrategy() {

  override val ranksPerBlock: Boolean
    get() = true
}

/**
 * A list of interchangeable [CheckerFactory]s DSS can run a block's analysis with, plus the
 * (pluggable) policy for which one to hand out on any given call to [next].
 * [PredicateBlockBehavior] calls [next] fresh on every recheck - not once per block - so
 * "interchangeable" matters: [next]'s caller always uses whatever it returns as a complete, correct
 * analysis on its own, with no expectation that consecutive calls return the same checker or that
 * any one checker's own state carries over from a previous call. [checkers] should therefore be
 * several instances/configurations of an analysis validated to converge the same way
 * `PredicateBlockBehavior`'s own soundness argument already assumes (see its class doc) - e.g. the
 * same CEGAR config built fresh each time, or configs that differ only in ways that don't change
 * what a sound, exact predicate-abstraction check would find reachable (a different solver, say).
 * Mixing genuinely different analysis *strategies* in one roster - ones that could soundly compute
 * incomparable over-approximations for the same input - is an unproven extension this class's own
 * contract doesn't cover: `recheck()`'s dedup check is structural-equality-based, not
 * semantic-entailment-based, so two disagreeing-but-both-sound checkers could in principle keep
 * "changing their mind" forever on a cyclic block and starve quiescence detection. Not a concern
 * for a roster of equivalent configurations, which is what this was built and tested for.
 *
 * **Must be constructed exactly once per DSS run, and that one instance shared by every block** -
 * not rebuilt inside a `behaviorFor = { block -> ... }` lambda, which runs once per block. Building
 * it per-block would silently give each block its own independent [strategy] instance (its own
 * round-robin cursor starting fresh at zero), breaking "balanced across the whole run" while still
 * looking correct in any single-checker test, since a list of one is trivially "balanced"
 * regardless.
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
