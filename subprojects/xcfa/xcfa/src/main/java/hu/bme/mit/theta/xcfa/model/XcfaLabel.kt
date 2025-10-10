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

import hu.bme.mit.theta.common.dsl.Env
import hu.bme.mit.theta.common.dsl.Scope
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.NonDetStmt
import hu.bme.mit.theta.core.stmt.SequenceStmt
import hu.bme.mit.theta.core.stmt.Stmt
import hu.bme.mit.theta.core.stmt.Stmts.*
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.grammar.dsl.expr.ExpressionWrapper
import hu.bme.mit.theta.grammar.dsl.stmt.StatementWrapper
import hu.bme.mit.theta.xcfa.model.RWLockReadLockLabel.Companion.readHandle
import hu.bme.mit.theta.xcfa.model.RWLockWriteLockLabel.Companion.writeHandle
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

// data class FenceLabel(val labels: Set<String>, override val metadata: MetaData = EmptyMetaData) :
//  XcfaLabel(metadata = metadata) {
//
//  override fun toString(): String {
//    return "F[${labels.joinToString(";")}]"
//  }
//
//  companion object {
//
//    fun fromString(s: String, scope: Scope, env: Env, metadata: MetaData): XcfaLabel {
//      val (labelList) = Regex("^F\\[(.*)]$").matchEntire(s)!!.destructured
//      return FenceLabel(labelList.split(";").toSet(), metadata = metadata)
//    }
//  }
// }

sealed class FenceLabel(
  open val handle: VarDecl<*>,
  override val metadata: MetaData = EmptyMetaData,
) : XcfaLabel(metadata) {
  open val acquiredMutexes: Set<VarDecl<*>> = setOf()
  open val releasedMutexes: Set<VarDecl<*>> = setOf()
  open val blockingMutexes: Set<VarDecl<*>> = setOf()
  val blockingMutexesWithoutAtomic: Set<VarDecl<*>>
    get() = blockingMutexes.filter { it != AtomicFenceLabel.ATOMIC_MUTEX }.toSet()

  protected abstract val label: String

  override fun toString(): String = "F[$label(${handle.name})]"
}

sealed class AtomicFenceLabel(override val metadata: MetaData = EmptyMetaData) :
  FenceLabel(handle = ATOMIC_MUTEX, metadata) {

  override fun toString(): String = "F[$label]"

  companion object {
    val ATOMIC_MUTEX: VarDecl<*> = Decls.Var("__theta_atomic_mutex__", Int())
  }
}

data class AtomicBeginLabel(override val metadata: MetaData = EmptyMetaData) :
  AtomicFenceLabel(metadata) {

  override val acquiredMutexes = setOf(ATOMIC_MUTEX)
  override val blockingMutexes = setOf(ATOMIC_MUTEX)
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

data class MutexLockLabel(
  override val handle: VarDecl<*>,
  override val metadata: MetaData = EmptyMetaData,
) : FenceLabel(handle, metadata) {

  override val acquiredMutexes = setOf(handle)
  override val blockingMutexes = setOf(handle, AtomicFenceLabel.ATOMIC_MUTEX)
  override val label = LABEL

  override fun toString(): String = super.toString()

  companion object {

    private const val LABEL = "mutex_lock"

    @Suppress("unused")
    fun fromString(s: String, scope: Scope, env: Env, metadata: MetaData): XcfaLabel {
      val (mutexName) = Regex("^F\\[$LABEL\\((.*)\\)]$").matchEntire(s)!!.destructured
      val mutexVar = env.eval(scope.resolve(mutexName).orElseThrow()) as VarDecl<*>
      return MutexLockLabel(mutexVar, metadata = metadata)
    }
  }
}

data class MutexUnlockLabel(
  override val handle: VarDecl<*>,
  override val metadata: MetaData = EmptyMetaData,
) : FenceLabel(handle, metadata) {

  override val releasedMutexes = setOf(handle)
  override val label = LABEL

  override fun toString(): String = super.toString()

  companion object {

    private const val LABEL = "mutex_unlock"

    @Suppress("unused")
    fun fromString(s: String, scope: Scope, env: Env, metadata: MetaData): XcfaLabel {
      val (mutexName) = Regex("^F\\[$LABEL\\((.*)\\)]$").matchEntire(s)!!.destructured
      val mutexVar = env.eval(scope.resolve(mutexName).orElseThrow()) as VarDecl<*>
      return MutexUnlockLabel(mutexVar, metadata = metadata)
    }
  }
}

data class MutexTryLockLabel(
  override val handle: VarDecl<*>,
  val successVar: VarDecl<*>,
  override val metadata: MetaData = EmptyMetaData,
) : FenceLabel(handle, metadata) {

  override val acquiredMutexes = setOf(handle)
  override val label = LABEL

  override fun toString(): String = "F[$label(${handle.name}, ${successVar.name})]"

  companion object {

    private const val LABEL = "mutex_trylock"

    @Suppress("unused")
    fun fromString(s: String, scope: Scope, env: Env, metadata: MetaData): XcfaLabel {
      val (mutexName, successVarName) =
        Regex("^F\\[$LABEL\\((.*), (.*)\\)]$").matchEntire(s)!!.destructured
      val mutexVar = env.eval(scope.resolve(mutexName).orElseThrow()) as VarDecl<*>
      val successVar = env.eval(scope.resolve(successVarName).orElseThrow()) as VarDecl<*>
      return MutexTryLockLabel(mutexVar, successVar, metadata = metadata)
    }
  }
}

data class RWLockReadLockLabel(
  override val handle: VarDecl<*>,
  override val metadata: MetaData = EmptyMetaData,
) : FenceLabel(handle, metadata) {

  override val acquiredMutexes = setOf(handle.readHandle)
  override val blockingMutexes = setOf(handle.writeHandle, AtomicFenceLabel.ATOMIC_MUTEX)
  override val label = LABEL

  override fun toString(): String = super.toString()

  companion object {

    private const val LABEL = "rwlock_read_lock"

    internal val readHandles: MutableMap<VarDecl<*>, VarDecl<*>> = mutableMapOf()
    internal val VarDecl<*>.readHandle: VarDecl<*>
      get() = readHandles.getOrPut(this) {
        Decls.Var("${this.name}__read_handle__", Int())
      }

    @Suppress("unused")
    fun fromString(s: String, scope: Scope, env: Env, metadata: MetaData): XcfaLabel {
      val (mutexName) = Regex("^F\\[$LABEL\\((.*)\\)]$").matchEntire(s)!!.destructured
      val mutexVar = env.eval(scope.resolve(mutexName).orElseThrow()) as VarDecl<*>
      return RWLockReadLockLabel(mutexVar, metadata = metadata)
    }
  }
}

data class RWLockWriteLockLabel(
  override val handle: VarDecl<*>,
  override val metadata: MetaData = EmptyMetaData,
) : FenceLabel(handle, metadata) {

  override val acquiredMutexes = setOf(handle.writeHandle)
  override val blockingMutexes = setOf(handle.writeHandle, handle.readHandle, AtomicFenceLabel.ATOMIC_MUTEX)
  override val label = LABEL

  override fun toString(): String = super.toString()

  companion object {

    private const val LABEL = "rwlock_write_lock"

    internal val writeHandles: MutableMap<VarDecl<*>, VarDecl<*>> = mutableMapOf()
    internal val VarDecl<*>.writeHandle: VarDecl<*>
      get() = writeHandles.getOrPut(this) {
        Decls.Var("${this.name}__write_handle__", this.type)
      }

    @Suppress("unused")
    fun fromString(s: String, scope: Scope, env: Env, metadata: MetaData): XcfaLabel {
      val (mutexName) = Regex("^F\\[$LABEL\\((.*)\\)]$").matchEntire(s)!!.destructured
      val mutexVar = env.eval(scope.resolve(mutexName).orElseThrow()) as VarDecl<*>
      return RWLockWriteLockLabel(mutexVar, metadata = metadata)
    }
  }
}

data class RWLockUnlockLabel(
  override val handle: VarDecl<*>,
  override val metadata: MetaData = EmptyMetaData,
) : FenceLabel(handle, metadata) {

  override val releasedMutexes = setOf(handle.readHandle, handle.writeHandle)
  override val label = LABEL

  override fun toString(): String = super.toString()

  companion object {

    private const val LABEL = "rwlock_unlock"

    @Suppress("unused")
    fun fromString(s: String, scope: Scope, env: Env, metadata: MetaData): XcfaLabel {
      val (mutexName) = Regex("^F\\[$LABEL\\((.*)\\)]$").matchEntire(s)!!.destructured
      val mutexVar = env.eval(scope.resolve(mutexName).orElseThrow()) as VarDecl<*>
      return RWLockUnlockLabel(mutexVar, metadata = metadata)
    }
  }
}

data class SequenceLabel
@JvmOverloads
constructor(val labels: List<XcfaLabel>, override val metadata: MetaData = EmptyMetaData) :
  XcfaLabel(metadata = metadata) {

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
