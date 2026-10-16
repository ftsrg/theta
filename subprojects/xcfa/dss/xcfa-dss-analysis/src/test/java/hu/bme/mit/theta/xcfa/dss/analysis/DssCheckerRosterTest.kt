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

import hu.bme.mit.theta.xcfa.model.XCFA
import java.util.concurrent.CountDownLatch
import java.util.concurrent.atomic.AtomicIntegerArray
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertThrows
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

/**
 * Pure selection tests with stub checkers that are never invoked; `PredicateBlockBehaviorTest`
 * covers the same distribution guarantee end to end with real checks.
 */
class DssCheckerRosterTest {

  /** One distinct, never-invoked [CheckerFactory] per index, identifiable by reference identity. */
  private fun stubCheckers(count: Int): List<CheckerFactory> =
    List(count) { i -> { _: XCFA -> error("stub checker $i must never actually be invoked") } }

  @Test
  fun `round-robin cycles through the list in order and wraps around`() {
    val checkers = stubCheckers(3)
    val roster = DssCheckerRoster(checkers)
    val selectedIndices = List(7) { checkers.indexOf(roster.next()) }
    assertEquals(listOf(0, 1, 2, 0, 1, 2, 0), selectedIndices)
  }

  @Test
  fun `round-robin usage counts differ by at most one for an uneven total`() {
    val checkers = stubCheckers(3)
    val roster = DssCheckerRoster(checkers)
    val counts = IntArray(3)
    repeat(20) { counts[checkers.indexOf(roster.next())]++ }
    assertEquals(20, counts.sum())
    assertTrue(counts.max() - counts.min() <= 1) {
      "expected balanced usage, got ${counts.toList()}"
    }
  }

  @Test
  fun `rejects an empty checker list`() {
    assertThrows(IllegalArgumentException::class.java) { DssCheckerRoster(emptyList()) }
  }

  @Test
  fun `a custom selection strategy is actually consulted, proving selection is changeable`() {
    val checkers = stubCheckers(3)
    val alwaysFirst =
      object : DssCheckerSelectionStrategy {
        override fun select(checkers: List<CheckerFactory>): CheckerFactory = checkers[0]
      }
    val roster = DssCheckerRoster(checkers, alwaysFirst)
    repeat(5) { assertEquals(0, checkers.indexOf(roster.next())) }
  }

  @Test
  fun `rejects a strategy that returns a checker not present in the roster`() {
    val checkers = stubCheckers(2)
    val rogue =
      object : DssCheckerSelectionStrategy {
        override fun select(checkers: List<CheckerFactory>): CheckerFactory = { _: XCFA ->
          error("never invoked - not one of the roster's own checkers")
        }
      }
    val roster = DssCheckerRoster(checkers, rogue)
    assertThrows(IllegalArgumentException::class.java) { roster.next() }
  }

  /**
   * One well-parallelized run is enough: balance follows from `AtomicInteger.getAndIncrement` being
   * linearizable, so this only guards against regressions (e.g. a non-atomic cursor).
   */
  @Test
  fun `concurrent selection from many threads still produces an exact, race-free distribution`() {
    val checkerCount = 4
    val threadCount = 8
    val callsPerThread = 250
    val checkers = stubCheckers(checkerCount)
    val roster = DssCheckerRoster(checkers)
    val counts = AtomicIntegerArray(checkerCount)
    val ready = CountDownLatch(threadCount)
    val start = CountDownLatch(1)
    val threads =
      List(threadCount) {
        Thread {
            ready.countDown()
            start.await()
            repeat(callsPerThread) { counts.incrementAndGet(checkers.indexOf(roster.next())) }
          }
          .apply { isDaemon = true }
      }
    threads.forEach { it.start() }
    ready.await()
    start.countDown()
    threads.forEach { it.join(10_000) }

    val allCounts = List(checkerCount) { counts.get(it) }
    assertEquals(threadCount * callsPerThread, allCounts.sum()) {
      "every call should be counted exactly once - lost/duplicate updates would show up here"
    }
    assertTrue(allCounts.max() - allCounts.min() <= 1) {
      "expected round-robin usage to differ by at most 1 even under concurrency, got $allCounts"
    }
  }
}
