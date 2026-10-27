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
package hu.bme.mit.theta.xcfa.analysis

import hu.bme.mit.theta.analysis.State
import hu.bme.mit.theta.core.type.BvLitExpr
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.IntLitExpr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.utils.BvUtils
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.model.AtomicFenceLabel.Companion.ATOMIC_MUTEX
import hu.bme.mit.theta.xcfa.model.MutexType.RECURSIVE
import java.math.BigInteger

/**
 * @param mutexes maps each lock to its owning process IDs and their positive acquisition counts.
 * @param mutexAttributes maps both attribute-object addresses to their current attributes and mutex
 *   addresses to the attribute snapshots copied at initialization. Missing mutex entries use
 *   NORMAL.
 */
data class MutexState(
  val mutexes: Map<MutexLock, Map<Int, Int>> = emptyMap(),
  val mutexAttributes: Map<LitExpr<*>, MutexAttribute> = emptyMap(),
) {

  init {
    check((mutexes[ATOMIC_MUTEX]?.size ?: 0) <= 1) {
      "Atomic mutex can be held by at most one process, but ${mutexes[ATOMIC_MUTEX]} hold it."
    }
    check(mutexes.values.all { holders -> holders.isNotEmpty() && holders.values.all { it > 0 } }) {
      "Mutexes must have owners with positive lock counts: $mutexes"
    }
  }

  internal fun enter(label: FenceLabel, pid: Int, state: State): MutexState? {
    val acquired = label.acquiredMutexes(state)
    check(acquired.all { it.isKnown() }) { "Ambiguous mutex lock is not supported." }
    if (
      label.blockingMutexes(state).any { mutex ->
        mutexes[mutex]?.let { holders ->
          val reentrant =
            mutex == ATOMIC_MUTEX ||
              (mutex is SimpleMutexLock && mutexAttributes[mutex.lock]?.type == RECURSIVE)
          !reentrant || holders.keys.any { it != pid }
        } ?: false
      }
    )
      return null

    val newMutexes = mutexes.toMutableMap()
    acquired.forEach { mutex ->
      val holders = newMutexes[mutex].orEmpty()
      // Atomic blocks retain their existing semantics: one end releases nested begins.
      val count = if (mutex == ATOMIC_MUTEX) 1 else (holders[pid] ?: 0) + 1
      newMutexes[mutex] = holders + (pid to count)
    }
    return copy(mutexes = newMutexes)
  }

  internal fun exit(label: FenceLabel, pid: Int, state: State): MutexState {
    val newMutexes = mutexes.toMutableMap()
    label.releasedMutexes(state).forEach { mutex ->
      check(mutex.isKnown()) { "Ambiguous mutex release is not supported." }
      val holders = newMutexes[mutex] ?: return@forEach
      val count = holders[pid] ?: return@forEach
      val remaining = if (count > 1) holders + (pid to count - 1) else holders - pid
      if (remaining.isEmpty()) newMutexes.remove(mutex) else newMutexes[mutex] = remaining
    }
    return copy(mutexes = newMutexes)
  }

  internal fun apply(label: InvokeLabel, state: State): MutexState {
    if (label.name !in libraryFunctions) return this

    fun Expr<*>.address(kind: String): LitExpr<*> =
      checkNotNull(simplify(state)) { "Unknown $kind address: $this" }

    val address =
      label.params[1].address(
        if (label.name == "pthread_mutex_init") "mutex" else "mutex attributes"
      )
    return when (label.name) {
      "pthread_mutexattr_init" ->
        copy(mutexAttributes = mutexAttributes + (address to MutexAttribute()))

      "pthread_mutexattr_settype" -> {
        val type =
          when (val value = label.params[2].simplify(state)) {
            is IntLitExpr -> value.value
            is BvLitExpr -> BvUtils.neutralBvLitExprToBigInteger(value)
            else -> error("Unknown mutex type: ${label.params[2]}")
          }
        val mutexType = MutexType.fromConstant(type)
        val attribute = (mutexAttributes[address] ?: MutexAttribute()).copy(type = mutexType)
        copy(mutexAttributes = mutexAttributes + (address to attribute))
      }

      "pthread_mutexattr_destroy" -> copy(mutexAttributes = mutexAttributes - address)

      "pthread_mutex_init" -> {
        val attrAddress = label.params[2].address("mutex attributes")
        val isNull =
          when (attrAddress) {
            is IntLitExpr -> attrAddress.value == BigInteger.ZERO
            is BvLitExpr -> BvUtils.neutralBvLitExprToBigInteger(attrAddress) == BigInteger.ZERO
            else -> false
          }
        val attribute =
          if (isNull) MutexAttribute()
          else
            checkNotNull(mutexAttributes[attrAddress]) {
              "Uninitialized mutex attributes: $attrAddress"
            }
        copy(mutexAttributes = mutexAttributes + (address to attribute))
      }

      else -> this
    }
  }

  companion object {
    private val libraryFunctions =
      setOf(
        "pthread_mutex_init",
        "pthread_mutexattr_init",
        "pthread_mutexattr_settype",
        "pthread_mutexattr_destroy",
      )
  }
}
