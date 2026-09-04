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
package hu.bme.mit.theta.xcfa.model

import hu.bme.mit.theta.analysis.State
import hu.bme.mit.theta.common.dsl.Env
import hu.bme.mit.theta.common.dsl.Scope
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.NonDetStmt
import hu.bme.mit.theta.core.stmt.SequenceStmt
import hu.bme.mit.theta.core.stmt.Stmt
import hu.bme.mit.theta.core.stmt.Stmts.*
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.grammar.dsl.expr.ExpressionWrapper
import hu.bme.mit.theta.grammar.dsl.stmt.StatementWrapper
import hu.bme.mit.theta.xcfa.model.ReadWriteMutexLock.ReadWriteMutexLockType.READ
import hu.bme.mit.theta.xcfa.model.ReadWriteMutexLock.ReadWriteMutexLockType.WRITE
import hu.bme.mit.theta.xcfa.utils.AssignStmtLabel
import java.util.*

sealed class XcfaLabel(open val metadata: MetaData) {

  open fun toStmt(): Stmt = Skip()
}

data class InvokeLabel
@JvmOverloads
constructor(
  val name: String,
  val params: List<Expr<*>>,
  override val metadata: MetaData,
  val tempLookup: Map<VarDecl<*>, VarDecl<*>> = emptyMap(),
  var isLibraryFunction: Boolean = false, // true means that passes/analyses should handle it
) : XcfaLabel(metadata) {

  override fun toString(): String {
    val sj = StringJoiner(", ", "(", ")")
    params.forEach { sj.add(it.toString()) }
    return "$name$sj"
  }

  companion object {

    @Suppress("unused")
    fun fromString(s: String, scope: Scope, env: Env, metadata: MetaData): XcfaLabel {
      val (name, params) = Regex("^([^(]*)\\((.*)\\)$").matchEntire(s)!!.destructured
      return InvokeLabel(
        name,
        params.split(",").map { ExpressionWrapper(scope, it).instantiate(env) },
        metadata = metadata,
      )
    }
  }
}

data class ReturnLabel(val enclosedLabel: XcfaLabel) :
  XcfaLabel(metadata = enclosedLabel.metadata) {

  override fun toStmt(): Stmt = enclosedLabel.toStmt()

  override fun toString(): String = "Return ($enclosedLabel)"
}

data class StartLabel(
  val name: String,
  val params: List<Expr<*>>,
  val pidVar: VarDecl<*>,
  override val metadata: MetaData,
  val tempLookup: Map<VarDecl<*>, VarDecl<*>> = emptyMap(),
) : XcfaLabel(metadata = metadata) {

  override fun toString(): String {
    val sj = StringJoiner(", ", "(", ")")
    params.forEach { sj.add(it.toString()) }
    return "$pidVar = start $name$sj"
  }

  companion object {

    @Suppress("unused")
    fun fromString(s: String, scope: Scope, env: Env, metadata: MetaData): XcfaLabel {
      val (pidVarName, pidVarType, name, params) =
        Regex("^\\(var (.*) (.*)\\) = start ([^(]*)\\((.*)\\)$").matchEntire(s)!!.destructured
      val pidVar = env.eval(scope.resolve(pidVarName).orElseThrow()) as VarDecl<*>
      return StartLabel(
        name,
        params.split(",").map { ExpressionWrapper(scope, it).instantiate(env) },
        pidVar,
        metadata = metadata,
      )
    }
  }
}

data class JoinLabel(val pidVar: VarDecl<*>, override val metadata: MetaData) :
  XcfaLabel(metadata = metadata) {

  override fun toString(): String = "join $pidVar"

  companion object {

    @Suppress("unused")
    fun fromString(s: String, scope: Scope, env: Env, metadata: MetaData): XcfaLabel {
      val (pidVarName, pidVarType) =
        Regex("^join \\(var (.*) (.*)\\)$").matchEntire(s)!!.destructured
      val pidVar = env.eval(scope.resolve(pidVarName).orElseThrow()) as VarDecl<*>
      return JoinLabel(pidVar, metadata = metadata)
    }
  }
}

enum class ChoiceType {
  NONE,
  MAIN_PATH,
  ALTERNATIVE_PATH,
}

data class StmtLabel
@JvmOverloads
constructor(
  val stmt: Stmt,
  val choiceType: ChoiceType = ChoiceType.NONE,
  override val metadata: MetaData = EmptyMetaData,
) : XcfaLabel(metadata = metadata) {

  init {
    check(stmt !is NonDetStmt && stmt !is SequenceStmt) {
      "NonDetStmt and SequenceStmt are not supported in XCFA. Use the corresponding labels instead."
    }
  }

  override fun toStmt(): Stmt = stmt

  override fun toString(): String =
    if (choiceType != ChoiceType.NONE) "($stmt)[choiceType=$choiceType]" else stmt.toString()

  companion object {

    @Suppress("unused")
    fun fromString(s: String, scope: Scope, env: Env, metadata: MetaData): XcfaLabel {
      val matchResult = Regex("^\\((.*)\\)\\[choiceType=(.*)]$").matchEntire(s)
      if (matchResult != null) {
        val (stmt, choiceTypeStr) = matchResult.destructured
        return StmtLabel(
          StatementWrapper(stmt, scope).instantiate(env),
          choiceType = ChoiceType.valueOf(choiceTypeStr),
          metadata = metadata,
        )
      } else {
        return StmtLabel(
          StatementWrapper(s, scope).instantiate(env),
          choiceType = ChoiceType.NONE,
          metadata = metadata,
        )
      }
    }
  }
}

sealed class FenceLabel(
  open val lock: Expr<*>,
  override val metadata: MetaData = EmptyMetaData,
) : XcfaLabel(metadata) {
  open val acquiredMutexes: Set<MutexLock> = setOf()
  open val releasedMutexes: Set<MutexLock> = setOf()
  val blockingMutexes: Set<MutexLock> // note: atomic implicitly blocks everything
    get() = acquiredMutexes.flatMap { it.blockingMutexLocks }.toSet()

  private fun Collection<MutexLock>.simplify(s: State): Set<MutexLock> =
    map { it.toFixedMutexLock(s) ?: it }.toSet()

  open fun acquiredMutexes(s: State): Set<MutexLock> = acquiredMutexes.simplify(s)
  open fun releasedMutexes(s: State): Set<MutexLock> = releasedMutexes.simplify(s)
  open fun blockingMutexes(s: State): Set<MutexLock> = blockingMutexes.simplify(s)

  protected abstract val label: String

  open fun preLabel(s: State): XcfaLabel = NopLabel

  override fun toString(): String = "F[$label(${lock})]"
}

sealed class AtomicFenceLabel(override val metadata: MetaData = EmptyMetaData) :
  FenceLabel(lock = ATOMIC_MUTEX_EXPR, metadata) {

  override fun toString(): String = "F[$label]"

  companion object {
    val ATOMIC_MUTEX_EXPR: IntLitExpr = Int(0)
    val ATOMIC_MUTEX: FixedMutexLock = SimpleFixedMutexLock(ATOMIC_MUTEX_EXPR)
  }
}

data class AtomicBeginLabel(override val metadata: MetaData = EmptyMetaData) :
  AtomicFenceLabel(metadata) {

  override val acquiredMutexes = setOf(ATOMIC_MUTEX)
  override val label = "ATOMIC_BEGIN"

  override fun toString(): String = super.toString()

  companion object {

    @Suppress("unused")
    fun fromString(s: String, scope: Scope, env: Env, metadata: MetaData): XcfaLabel {
      if (s != AtomicBeginLabel().toString()) {
        throw IllegalArgumentException("Invalid AtomicBeginLabel string: $s")
      }
      return AtomicBeginLabel(metadata = metadata)
    }
  }
}

data class AtomicEndLabel(override val metadata: MetaData = EmptyMetaData) :
  AtomicFenceLabel(metadata) {

  override val releasedMutexes = setOf(ATOMIC_MUTEX)
  override val label = "ATOMIC_END"

  override fun toString(): String = super.toString()

  companion object {

    @Suppress("unused")
    fun fromString(s: String, scope: Scope, env: Env, metadata: MetaData): XcfaLabel {
      if (s != AtomicEndLabel().toString()) {
        throw IllegalArgumentException("Invalid AtomicEndLabel string: $s")
      }
      return AtomicEndLabel(metadata = metadata)
    }
  }
}

sealed class LockLabel(
  lock: Expr<*>,
  metadata: MetaData,
  open val lockVar: VarDecl<*>?,
) : FenceLabel(lock, metadata) {

  override fun preLabel(s: State): XcfaLabel =
      if (lockExpr.lockToLiteral(s) is IntLitExpr) super.preLabel(s)
      else AssignStmtLabel(lockVar!!.ref, lock)

  protected val lockExpr: Expr<*> = lockVar?.ref ?: lock

  abstract fun lockedMutexes(lockExpr: Expr<*>): Set<MutexLock>

  override val acquiredMutexes: Set<MutexLock> = lockedMutexes(lockExpr)

  override fun acquiredMutexes(s: State): Set<MutexLock> =
    lockExpr.lockToLiteral(s)?.let { lockedMutexes(it) } ?: super.acquiredMutexes(s)

  override fun blockingMutexes(s: State): Set<MutexLock> =
    acquiredMutexes(s).flatMap { it.blockingMutexLocks }.toSet()

  companion object {
    private var lockCounter = 0

    @JvmStatic
    protected fun <T : Type> getLockVar(lock: Expr<T>): VarDecl<T>? =
      if (lock is LitExpr<*>) null
      else Decls.Var("__theta_lock_${lockCounter++}", lock.type)
  }
}

data class MutexLockLabel(
  override val lock: Expr<*>,
  override val metadata: MetaData = EmptyMetaData,
  override val lockVar: VarDecl<*>? = getLockVar(lock),
) : LockLabel(lock, metadata, lockVar) {

  override fun lockedMutexes(lockExpr: Expr<*>): Set<MutexLock> =
    setOf(SimpleMutexLock.of(lockExpr))

  override val label = LABEL

  override fun toString(): String = super.toString()

  companion object {

    private const val LABEL = "mutex_lock"

    @Suppress("unused")
    fun fromString(s: String, scope: Scope, env: Env, metadata: MetaData): XcfaLabel {
      val (mutexHandle) = Regex("^F\\[$LABEL\\((.*)\\)]$").matchEntire(s)!!.destructured
      val expr = ExpressionWrapper(scope, mutexHandle).instantiate(env)
      return MutexLockLabel(cast(expr, Int()), metadata = metadata)
    }
  }
}

data class MutexUnlockLabel(
  override val lock: Expr<*>,
  override val metadata: MetaData = EmptyMetaData,
) : FenceLabel(lock, metadata) {

  override val releasedMutexes = setOf(SimpleMutexLock.of(lock))
  override val label = LABEL

  override fun toString(): String = super.toString()

  companion object {

    private const val LABEL = "mutex_unlock"

    @Suppress("unused")
    fun fromString(s: String, scope: Scope, env: Env, metadata: MetaData): XcfaLabel {
      val (mutexHandle) = Regex("^F\\[$LABEL\\((.*)\\)]$").matchEntire(s)!!.destructured
      val expr = ExpressionWrapper(scope, mutexHandle).instantiate(env)
      return MutexUnlockLabel(cast(expr, Int()), metadata = metadata)
    }
  }
}

data class MutexTryLockLabel(
  override val lock: Expr<*>,
  val successVar: VarDecl<*>,
  override val metadata: MetaData = EmptyMetaData,
  override val lockVar: VarDecl<*>? = getLockVar(lock),
) : LockLabel(lock, metadata, lockVar) {

  override fun lockedMutexes(lockExpr: Expr<*>): Set<MutexLock> =
    setOf(SimpleMutexLock.of(lockExpr))

  override val label = LABEL

  override fun toString(): String = "F[$label(${lock}, ${successVar.name})]"

  companion object {

    private const val LABEL = "mutex_trylock"

    @Suppress("unused")
    fun fromString(s: String, scope: Scope, env: Env, metadata: MetaData): XcfaLabel {
      val (mutexHandle, successVarName) =
        Regex("^F\\[$LABEL\\((.*), (.*)\\)]$").matchEntire(s)!!.destructured
      val expr = ExpressionWrapper(scope, mutexHandle).instantiate(env)
      val successVar = env.eval(scope.resolve(successVarName).orElseThrow()) as VarDecl<*>
      return MutexTryLockLabel(cast(expr, Int()), successVar, metadata = metadata)
    }
  }
}

data class RWLockReadLockLabel(
  override val lock: Expr<*>,
  override val metadata: MetaData = EmptyMetaData,
  override val lockVar: VarDecl<*>? = getLockVar(lock),
) : LockLabel(lock, metadata, lockVar) {

  override fun lockedMutexes(lockExpr: Expr<*>): Set<MutexLock> =
    setOf(ReadWriteMutexLock.of(lockExpr, READ))

  override val label = LABEL

  override fun toString(): String = super.toString()

  companion object {

    private const val LABEL = "rwlock_read_lock"

    @Suppress("unused")
    fun fromString(s: String, scope: Scope, env: Env, metadata: MetaData): XcfaLabel {
      val (mutexHandle) = Regex("^F\\[$LABEL\\((.*)\\)]$").matchEntire(s)!!.destructured
      val expr = ExpressionWrapper(scope, mutexHandle).instantiate(env)
      return RWLockReadLockLabel(cast(expr, Int()), metadata = metadata)
    }
  }
}

data class RWLockWriteLockLabel(
  override val lock: Expr<*>,
  override val metadata: MetaData = EmptyMetaData,
  override val lockVar: VarDecl<*>? = getLockVar(lock),
) : LockLabel(lock, metadata, lockVar) {

  override fun lockedMutexes(lockExpr: Expr<*>): Set<MutexLock> =
    setOf(ReadWriteMutexLock.of(lockExpr, WRITE))

  override val label = LABEL

  override fun toString(): String = super.toString()

  companion object {

    private const val LABEL = "rwlock_write_lock"

    @Suppress("unused")
    fun fromString(s: String, scope: Scope, env: Env, metadata: MetaData): XcfaLabel {
      val (mutexHandle) = Regex("^F\\[$LABEL\\((.*)\\)]$").matchEntire(s)!!.destructured
      val expr = ExpressionWrapper(scope, mutexHandle).instantiate(env)
      return RWLockWriteLockLabel(cast(expr, Int()), metadata = metadata)
    }
  }
}

data class RWLockUnlockLabel(
  override val lock: Expr<*>,
  override val metadata: MetaData = EmptyMetaData,
) : FenceLabel(lock, metadata) {

  override val releasedMutexes =
    setOf(ReadWriteMutexLock.of(lock, READ), ReadWriteMutexLock.of(lock, WRITE))
  override val label = LABEL

  override fun toString(): String = super.toString()

  companion object {

    private const val LABEL = "rwlock_unlock"

    @Suppress("unused")
    fun fromString(s: String, scope: Scope, env: Env, metadata: MetaData): XcfaLabel {
      val (mutexHandle) = Regex("^F\\[$LABEL\\((.*)\\)]$").matchEntire(s)!!.destructured
      val expr = ExpressionWrapper(scope, mutexHandle).instantiate(env)
      return RWLockUnlockLabel(cast(expr, Int()), metadata = metadata)
    }
  }
}

data class SequenceLabel
@JvmOverloads
constructor(val labels: List<XcfaLabel>, override val metadata: MetaData = EmptyMetaData) :
  XcfaLabel(metadata = metadata) {

  constructor(
    labels: Sequence<XcfaLabel>,
    metadata: MetaData = EmptyMetaData,
  ) : this(labels.toList(), metadata)

  override fun toStmt(): Stmt {
    return SequenceStmt(labels.filter { it !is NopLabel }.map { it.toStmt() })
  }

  override fun toString(): String {
    val sj = StringJoiner(",", "[", "]")
    labels.forEach { sj.add(it.toString()) }
    return sj.toString()
  }
}

data class NondetLabel
@JvmOverloads
constructor(val labels: Set<XcfaLabel>, override val metadata: MetaData = EmptyMetaData) :
  XcfaLabel(metadata = metadata) {

  override fun toStmt(): Stmt {
    return NonDetStmt(labels.map { it.toStmt() })
  }

  override fun toString(): String {
    return "NonDet($labels)"
  }
}

object NopLabel : XcfaLabel(metadata = EmptyMetaData) {

  override fun toStmt(): Stmt {
    return Skip()
  }

  override fun toString(): String {
    return "Nop"
  }
}

fun getTempLookup(label: XcfaLabel): Map<VarDecl<*>, VarDecl<*>> {
  return when (label) {
    is InvokeLabel -> {
      label.tempLookup
    }

    is StartLabel -> {
      label.tempLookup
    }

    is SequenceLabel -> {
      val lookup: MutableMap<VarDecl<*>, VarDecl<*>> = LinkedHashMap()
      for (sublabel in label.labels) {
        lookup.putAll(getTempLookup(sublabel))
      }
      lookup
    }

    is NondetLabel -> {
      val lookup: MutableMap<VarDecl<*>, VarDecl<*>> = LinkedHashMap()
      for (sublabel in label.labels) {
        lookup.putAll(getTempLookup(sublabel))
      }
      lookup
    }

    else -> emptyMap()
  }
}
