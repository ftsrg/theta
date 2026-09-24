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

package hu.bme.mit.theta.xcfa.model

import hu.bme.mit.theta.analysis.State
import hu.bme.mit.theta.analysis.WrapperState
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.xcfa.model.ReadWriteMutexLock.ReadWriteMutexLockType.READ
import hu.bme.mit.theta.xcfa.model.ReadWriteMutexLock.ReadWriteMutexLockType.WRITE

fun Collection<MutexLock>.known(): Set<MutexLock> = filter { it.isKnown() }.toSet()

internal fun Expr<*>.simplify(s: State): LitExpr<*>? =
  this as? LitExpr<*>
    ?: when (s) {
      is WrapperState -> simplify(s.wrappedState)
      is ExplState -> ExprUtils.simplify(this, s.`val`) as? LitExpr<*>
      else -> ExprUtils.simplify(this) as? LitExpr<*>
    }

sealed interface MutexLock {

  val lock: Expr<*>
  val blockingMutexLocks: Set<MutexLock>
    get() = setOf(this)

  fun isKnown(): Boolean = lock is LitExpr<*>

  fun simplify(s: State): MutexLock

  fun isEqual(other: MutexLock): Expr<BoolType>? = Eq(lock, other.lock)
}

data class SimpleMutexLock(override val lock: Expr<*>) : MutexLock {

  override fun simplify(s: State): SimpleMutexLock =
    lock.simplify(s)?.let { SimpleMutexLock(it) } ?: this

  override fun isEqual(other: MutexLock): Expr<BoolType>? {
    if (other !is SimpleMutexLock) return null
    return super.isEqual(other)
  }
}

data class ReadWriteMutexLock(override val lock: Expr<*>, val type: ReadWriteMutexLockType) :
  MutexLock {

  enum class ReadWriteMutexLockType {
    READ,
    WRITE,
  }

  override fun simplify(s: State): ReadWriteMutexLock =
    lock.simplify(s)?.let { ReadWriteMutexLock(it, type) } ?: this

  override val blockingMutexLocks: Set<ReadWriteMutexLock>
    get() =
      when (type) {
        READ -> setOf(copy(type = WRITE))
        WRITE -> setOf(this, copy(type = READ))
      }

  override fun isEqual(other: MutexLock): Expr<BoolType>? {
    if (other !is ReadWriteMutexLock) return null
    if (type != other.type) return null
    return super.isEqual(other)
  }
}
