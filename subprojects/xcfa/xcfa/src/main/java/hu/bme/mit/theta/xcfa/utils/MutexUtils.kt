/*
 *  Copyright 2025 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.xcfa.utils

import hu.bme.mit.theta.xcfa.model.FenceLabel
import hu.bme.mit.theta.xcfa.model.MutexLock
import hu.bme.mit.theta.xcfa.model.XcfaEdge
import hu.bme.mit.theta.xcfa.model.fixed

/** The set of mutexes acquired embedded into each other. */
inline val XcfaEdge.acquiredEmbeddedMutexes: Set<MutexLock>
  get() {
    val acquired = mutableSetOf<MutexLock>()
    val toVisit = mutableListOf<Pair<XcfaEdge, Set<MutexLock>>>(this to setOf())
    while (toVisit.isNotEmpty()) {
      val (visiting, mutexes) = toVisit.removeFirst()
      val newMutexes = mutexes.toMutableSet()
      acquired.addAll(
        visiting.getFlatLabels().filterIsInstance<FenceLabel>().flatMap { fence ->
          fence.acquiredMutexes
        }
      )
      if (visiting.mutexOperations(newMutexes)) {
        visiting.target.outgoingEdges.forEach { toVisit.add(it to newMutexes) }
      }
    }
    return acquired
  }

/**
 * Follows the mutex operations of the given edge and updates the given set of mutexes.
 *
 * @param mutexes the set of mutexes currently acquired
 * @return true if the set of mutexes is non-empty after the mutex operations
 */
fun XcfaEdge.mutexOperations(mutexes: MutableSet<MutexLock>): Boolean {
  val edgeFlatLabels = getFlatLabels()
  val acquiredLocks = mutableSetOf<MutexLock>()
  val releasedLocks = mutableSetOf<MutexLock>()
  edgeFlatLabels.filterIsInstance<FenceLabel>().forEach { fence ->
    val released = fence.releasedMutexes.fixed()
    releasedLocks.addAll(released)
    acquiredLocks.removeAll(released)

    acquiredLocks.addAll(fence.acquiredMutexes)
    releasedLocks.removeAll(fence.acquiredMutexes)
  }
  mutexes.removeAll(releasedLocks)
  mutexes.addAll(acquiredLocks)
  return mutexes.isNotEmpty()
}
