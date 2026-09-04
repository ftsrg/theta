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
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Neq
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.solver.Solver
import hu.bme.mit.theta.solver.utils.WithPushPop
import hu.bme.mit.theta.solver.z3.Z3SolverFactory
import hu.bme.mit.theta.xcfa.model.ReadWriteMutexLock.ReadWriteMutexLockType
import hu.bme.mit.theta.xcfa.model.ReadWriteMutexLock.ReadWriteMutexLockType.READ
import hu.bme.mit.theta.xcfa.model.ReadWriteMutexLock.ReadWriteMutexLockType.WRITE


fun Collection<MutexLock>.unknown(): Set<MutexLock> =
  filter { it !is FixedMutexLock }.toSet()

fun Collection<MutexLock>.fixed(): Set<MutexLock> =
  filterIsInstance<FixedMutexLock>().toSet()

internal fun Expr<*>.lockToLiteral(s: State): LitExpr<*>? =
  this as? LitExpr<*>
    ?: when (s) {
      is WrapperState -> lockToLiteral(s.wrappedState)
      is ExplState -> ExprUtils.simplify(this, s.`val`) as? LitExpr<*>
      is ExprState -> FixedMutexLock.getEntailedMutexLockFor(s, this)
      else -> ExprUtils.simplify(this) as? LitExpr<*>
    }

sealed interface MutexLock {

  val lock: Expr<*>
  val blockingMutexLocks: Set<MutexLock> get() = setOf(this)

  fun toFixedMutexLock(s : State): FixedMutexLock?
  fun isEqual(other: MutexLock): Expr<BoolType>? = Eq(lock, other.lock)
}

sealed interface FixedMutexLock : MutexLock {

  abstract override val lock: LitExpr<*>
  override val blockingMutexLocks: Set<FixedMutexLock> get() = setOf(this)
  override fun toFixedMutexLock(s: State): FixedMutexLock = this

  companion object {
    private val solver: Solver by lazy { Z3SolverFactory.getInstance().createSolver() }

    private val mutexLocks: MutableSet<LitExpr<*>> = mutableSetOf()

    // TODO register mutex initializations
    fun registerMutexObject(lock: LitExpr<*>) {
      mutexLocks.add(lock)
    }

    internal fun getEntailedMutexLockFor(state: ExprState, lock: Expr<*>): LitExpr<*>? {
      val entailed = mutableSetOf<LitExpr<*>>()
      mutexLocks.forEach { mutexLock ->
        val notEntailed =
          WithPushPop(solver).use {
            solver.add(state.toExpr())
            solver.add(Neq(lock, mutexLock))
            solver.check().isSat
          }
        if (!notEntailed) {
          entailed.add(mutexLock)
          if (entailed.size > 1) return null
        }
      }
      return if (entailed.size == 1) entailed.first() else null
    }
  }
}

sealed interface SimpleMutexLock : MutexLock {

  override fun toFixedMutexLock(s: State): SimpleFixedMutexLock?

  override fun isEqual(other: MutexLock): Expr<BoolType>? {
    if (other !is SimpleMutexLock) return null
    return super.isEqual(other)
  }

  companion object {

    fun of(lock: Expr<*>): SimpleMutexLock =
      if (lock is LitExpr<*>) SimpleFixedMutexLock(lock)
      else SimpleUnknownMutexLock(lock)
  }
}

@ConsistentCopyVisibility
data class SimpleUnknownMutexLock internal constructor(
  override val lock: Expr<*>,
) : SimpleMutexLock {

  override fun toFixedMutexLock(s: State): SimpleFixedMutexLock? =
    lock.lockToLiteral(s)?.let { SimpleFixedMutexLock(it) }
}

@ConsistentCopyVisibility
data class SimpleFixedMutexLock internal constructor(
  override val lock: LitExpr<*>,
) : SimpleMutexLock, FixedMutexLock {

  override fun toFixedMutexLock(s: State): SimpleFixedMutexLock = this
}

sealed interface ReadWriteMutexLock : MutexLock {

  val type: ReadWriteMutexLockType

  enum class ReadWriteMutexLockType {
    READ,
    WRITE
  }

  override val blockingMutexLocks: Set<ReadWriteMutexLock>

  override fun isEqual(other: MutexLock): Expr<BoolType>? {
    if (other !is ReadWriteMutexLock) return null
    if (type != other.type) return null
    return super.isEqual(other)
  }

  companion object {

    fun of(lock: Expr<*>, type: ReadWriteMutexLockType): ReadWriteMutexLock =
      if (lock is LitExpr<*>) ReadWriteFixedMutexLock(lock, type)
      else ReadWriteUnknownMutexLock(lock, type)
  }
}

@ConsistentCopyVisibility
data class ReadWriteUnknownMutexLock internal constructor(
  override val lock: Expr<*>,
  override val type: ReadWriteMutexLockType
) : ReadWriteMutexLock {

  override val blockingMutexLocks: Set<ReadWriteUnknownMutexLock>
    get() =
      when (type) {
        READ -> setOf(copy(type = WRITE))
        WRITE -> setOf(this, copy(type = READ))
      }

  override fun toFixedMutexLock(s: State): ReadWriteFixedMutexLock? =
    lock.lockToLiteral(s)?.let { ReadWriteFixedMutexLock(it, type) }
}

@ConsistentCopyVisibility
data class ReadWriteFixedMutexLock internal constructor(
  override val lock: LitExpr<*>,
  override val type: ReadWriteMutexLockType
) : ReadWriteMutexLock, FixedMutexLock {

  override val blockingMutexLocks: Set<ReadWriteFixedMutexLock>
    get() =
      when (type) {
        READ -> setOf(copy(type = WRITE))
        WRITE -> setOf(this, copy(type = READ))
      }
}