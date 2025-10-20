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
import hu.bme.mit.theta.xcfa.model.XcfaEdge
import hu.bme.mit.theta.xcfa.model.XcfaLabel

inline val XcfaLabel.isAtomicBegin: Boolean
  get() = this is FenceLabel && "ATOMIC_BEGIN" in labels
inline val XcfaLabel.isAtomicEnd: Boolean
  get() = this is FenceLabel && "ATOMIC_END" in labels

/** The set of mutexes acquired by the label. */
inline val FenceLabel.acquiredMutexes: Set<String>
  get() = labels.mapNotNull { it.acquiredMutex }.toSet()

inline val String.acquiredMutex: String?
  get() =
    when {
      this == "ATOMIC_BEGIN" -> ""
      startsWith("mutex_lock") -> substringAfter('(').substringBefore(')')
      startsWith("cond_wait") -> substring("cond_wait".length + 1, length - 1).split(",")[1]
      else -> null
    }

/** The set of mutexes released by the label. */
inline val FenceLabel.releasedMutexes: Set<String>
  get() = labels.mapNotNull { it.releasedMutex }.toSet()

inline val String.releasedMutex: String?
  get() =
    when {
      this == "ATOMIC_END" -> ""
      startsWith("mutex_unlock") -> substringAfter('(').substringBefore(')')
      startsWith("start_cond_wait") ->
        substring("start_cond_wait".length + 1, length - 1).split(",")[1]

      else -> null
    }

/** The set of mutexes acquired embedded into each other. */
inline val XcfaEdge.acquiredEmbeddedFenceVars: Set<String>
  get() {
    val acquired = mutableSetOf<String>()
    val toVisit = mutableListOf<Pair<XcfaEdge, Set<String>>>(this to setOf())
    while (toVisit.isNotEmpty()) {
      val (visiting, mutexes) = toVisit.removeFirst()
      val newMutexes = mutexes.toMutableSet()
      acquired.addAll(
        visiting.getFlatLabels().flatMap { fence ->
          if (fence !is FenceLabel) return@flatMap emptyList()
          fence.acquiredMutexes +
            fence.labels
              .filter { it.startsWith("start_cond_wait") }
              .map { it.substring("start_cond_wait".length + 1, it.length - 1).split(",")[0] }
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
fun XcfaEdge.mutexOperations(mutexes: MutableSet<String>): Boolean {
  val edgeFlatLabels = getFlatLabels()
  val acquiredLocks = mutableSetOf<String>()
  val releasedLocks = mutableSetOf<String>()
  edgeFlatLabels.filterIsInstance<FenceLabel>().forEach { fence ->
    releasedLocks.addAll(fence.releasedMutexes)
    acquiredLocks.removeAll(fence.releasedMutexes)

    acquiredLocks.addAll(fence.acquiredMutexes)
    releasedLocks.removeAll(fence.acquiredMutexes)
  }
  mutexes.removeAll(releasedLocks)
  mutexes.addAll(acquiredLocks)
  return mutexes.isNotEmpty()
}
