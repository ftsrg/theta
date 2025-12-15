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

import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.xcfa.model.FenceLabel
import hu.bme.mit.theta.xcfa.model.XcfaEdge

val XcfaEdge.fenceVars: Set<VarDecl<*>>
  get() = getFlatLabels().filterIsInstance<FenceLabel>().map { fence -> fence.handle }.toSet()

/** The set of mutexes acquired embedded into each other. */
inline val XcfaEdge.acquiredEmbeddedFenceVars: Set<VarDecl<*>>
  get() {
    val acquired = mutableSetOf<VarDecl<*>>()
    val toVisit = mutableListOf<Pair<XcfaEdge, Set<VarDecl<*>>>>(this to setOf())
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
fun XcfaEdge.mutexOperations(mutexes: MutableSet<VarDecl<*>>): Boolean {
  val edgeFlatLabels = getFlatLabels()
  val acquiredLocks = mutableSetOf<VarDecl<*>>()
  val releasedLocks = mutableSetOf<VarDecl<*>>()
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
