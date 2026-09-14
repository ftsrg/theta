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
package hu.bme.mit.theta.xcfa.cli.portfolio

import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import hu.bme.mit.theta.xcfa.model.XcfaProcedure

/**
 * Whether a bounded engine can *finish* on this program, rather than only look for a bug.
 *
 * Two things have to hold. No procedure's control-flow graph may contain a cycle, so every
 * execution is finite and a bounded check that reaches the longest path has proved safety outright
 * rather than guessed at it. And the unrolling that produced this XCFA has to have been exhaustive:
 * a force-unrolled loop is cycle-free only because the executions past the bound were dropped, and
 * the checkers already refuse a `safe` verdict in that case, so leading with a bounded engine would
 * spend the slice on an answer that cannot be returned.
 *
 * Only the shape of the graph is read, never the name of anything in it.
 */
internal val XCFA.boundedIsComplete: Boolean
  get() = !unsafeUnrollUsed && procedures.none { it.hasCycle() }

private fun XcfaProcedure.hasCycle(): Boolean {
  val successors = edges.groupBy({ it.source }, { it.target })
  val visited = mutableSetOf<XcfaLocation>()
  val onStack = mutableSetOf<XcfaLocation>()

  // Iterative DFS: a procedure inlined from deep recursion can nest further than the JVM stack.
  fun reachesCycleFrom(start: XcfaLocation): Boolean {
    if (start in visited) return false
    val stack = ArrayDeque<Pair<XcfaLocation, Iterator<XcfaLocation>>>()
    visited.add(start)
    onStack.add(start)
    stack.addLast(start to successors[start].orEmpty().iterator())
    while (stack.isNotEmpty()) {
      val (loc, iter) = stack.last()
      if (iter.hasNext()) {
        val next = iter.next()
        if (next in onStack) return true
        if (next !in visited) {
          visited.add(next)
          onStack.add(next)
          stack.addLast(next to successors[next].orEmpty().iterator())
        }
      } else {
        onStack.remove(loc)
        stack.removeLast()
      }
    }
    return false
  }

  return locs.any { reachesCycleFrom(it) }
}

/**
 * McCabe complexity summed over the procedures, as `E - N + 2` each.
 *
 * This is the sharpest single structural predictor of which algorithm wins, measured over the whole
 * suite: below about sixteen the predicate domains lead, above it the explicit domain does, and by
 * the largest programs it leads by half again. The reading is mechanical -- predicate abstraction
 * pays per predicate it has to discover, and the number of predicates a proof needs tracks the
 * branching structure, while explicit-value tracking is indifferent to it.
 *
 * Only the shape of the graph is counted, never the name of anything in it.
 */
internal val XCFA.cyclomaticComplexity: Int
  get() = procedures.sumOf { maxOf(0, it.edges.size - it.locs.size + 2) }

/** Above this the explicit domain is measurably the better opening move. */
internal const val EXPLICIT_FIRST_COMPLEXITY = 16
