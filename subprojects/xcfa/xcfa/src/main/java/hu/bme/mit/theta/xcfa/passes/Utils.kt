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
package hu.bme.mit.theta.xcfa.passes

import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.*
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import java.util.*

/** XcfaEdge must be in a `deterministic` ProcedureBuilder */
fun XcfaEdge.splitIf(function: (XcfaLabel) -> Boolean): List<XcfaEdge> {
  check(label is SequenceLabel)
  val newLabels = ArrayList<SequenceLabel>()
  var current = ArrayList<XcfaLabel>()
  for (label in label.labels) {
    if (function(label)) {
      if (current.isNotEmpty()) {
        newLabels.add(SequenceLabel(current))
        current = ArrayList()
      }
      newLabels.add(SequenceLabel(listOf(label)))
    } else {
      current.add(label)
    }
  }
  if (current.isNotEmpty()) newLabels.add(SequenceLabel(current))

  val locations = ArrayList<XcfaLocation>()
  locations.add(source)
  for (i in 2..(newLabels.size)) { // potentially metadata is off-by-one (i-2 might be suitable?)
    locations.add(
      XcfaLocation("loc" + XcfaLocation.uniqueCounter(), metadata = newLabels[i - 1].metadata)
    )
  }
  locations.add(target)

  val newEdges = ArrayList<XcfaEdge>()
  for ((i, label) in newLabels.withIndex()) {
    newEdges.add(XcfaEdge(locations[i], locations[i + 1], label, label.metadata))
  }
  return newEdges
}

fun Stmt.flatten(): List<Stmt> {
  return when (this) {
    is SequenceStmt -> stmts.map { it.flatten() }.flatten()
    is NonDetStmt -> listOf(this) // error prone because it might contain sequence stmts
    else -> listOf(this)
  }
}

@JvmOverloads
fun XcfaLabel.changeVars(
  varLut: Map<out Decl<*>, VarDecl<*>>,
  parseContext: ParseContext? = null,
): XcfaLabel =
  if (varLut.isNotEmpty())
    when (this) {
      is InvokeLabel ->
        InvokeLabel(
          name,
          params.map { it.changeVars(varLut, parseContext) },
          metadata = metadata,
          isLibraryFunction = isLibraryFunction,
        )

      is JoinLabel -> JoinLabel(pidVar.changeVars(varLut), metadata = metadata)
      is NondetLabel ->
        NondetLabel(labels.map { it.changeVars(varLut, parseContext) }.toSet(), metadata = metadata)

      is SequenceLabel ->
        SequenceLabel(labels.map { it.changeVars(varLut, parseContext) }, metadata = metadata)

      is StartLabel ->
        StartLabel(
          name,
          params.map { it.changeVars(varLut, parseContext) },
          pidVar.changeVars(varLut),
          metadata = metadata,
        )

      is StmtLabel ->
        StmtLabel(
          stmt.changeVars(varLut, parseContext),
          metadata = metadata,
          choiceType = this.choiceType,
        )

      is ReturnLabel -> ReturnLabel(enclosedLabel.changeVars(varLut))

      is FenceLabel -> {
        when (this) {
          is MutexLockLabel -> MutexLockLabel(handle.changeVars(varLut), metadata)
          is MutexTryLockLabel ->
            MutexTryLockLabel(handle.changeVars(varLut), successVar.changeVars(varLut), metadata)
          is MutexUnlockLabel -> MutexUnlockLabel(handle.changeVars(varLut), metadata)
          is RWLockReadLockLabel -> RWLockReadLockLabel(handle.changeVars(varLut), metadata)
          is RWLockWriteLockLabel -> RWLockWriteLockLabel(handle.changeVars(varLut), metadata)
          is RWLockUnlockLabel -> RWLockUnlockLabel(handle.changeVars(varLut), metadata)
          else -> this
        }
      }

      else -> this
    }
  else this

@JvmOverloads
fun Stmt.changeVars(
  varLut: Map<out Decl<*>, VarDecl<*>>,
  parseContext: ParseContext? = null,
): Stmt {
  val stmt =
    when (this) {
      is AssignStmt<*> ->
        AssignStmt.of(
          cast(varDecl.changeVars(varLut), varDecl.type),
          cast(expr.changeVars(varLut, parseContext), varDecl.type),
        )

      is MemoryAssignStmt<*, *, *> ->
        MemoryAssignStmt.create(
          deref.changeVars(varLut) as Dereference<out Type, *, *>,
          expr.changeVars(varLut),
        )

      is HavocStmt<*> -> HavocStmt.of(varDecl.changeVars(varLut))
      is AssumeStmt -> AssumeStmt.of(cond.changeVars(varLut, parseContext))
      is SequenceStmt -> SequenceStmt.of(stmts.map { it.changeVars(varLut, parseContext) })
      is SkipStmt -> this
      else -> TODO("Not yet implemented")
    }
  val metadataValue = parseContext?.getMetadata()?.getMetadataValue(this, "sourceStatement")
  if (metadataValue?.isPresent == true)
    parseContext.getMetadata().create(stmt, "sourceStatement", metadataValue.get())
  return stmt
}

@JvmOverloads
fun <T : Type> Expr<T>.changeVars(
  varLut: Map<out Decl<*>, VarDecl<*>>,
  parseContext: ParseContext? = null,
): Expr<T> =
  if (this is RefExpr<T>) (decl as Decl<T>).changeVars(varLut).ref
  else {
    val ret = this.withOps(this.ops.map { it.changeVars(varLut, parseContext) })
    if (parseContext?.metadata?.getMetadataValue(this, "cType")?.isPresent == true) {
      parseContext.metadata?.create(ret, "cType", CComplexType.getType(this, parseContext))
    }
    ret
  }

fun <T : Type> Decl<T>.changeVars(varLut: Map<out Decl<*>, VarDecl<*>>): Decl<T> =
  (varLut[this] as? Decl<T> ?: this)

fun <T : Type> VarDecl<T>.changeVars(varLut: Map<out Decl<*>, VarDecl<*>>): VarDecl<T> =
  (varLut[this] ?: this) as VarDecl<T>

@JvmOverloads
fun XcfaLabel.changeSubexpr(
  exprLut: Map<Expr<*>, Expr<*>>,
  parseContext: ParseContext? = null,
): XcfaLabel =
  if (exprLut.isNotEmpty()) {
    when (this) {
      is InvokeLabel -> copy(params = params.map { it.changeSubexpr(exprLut, parseContext) })

      is JoinLabel -> copy(pidVar = pidVar.changeSubexpr(exprLut))
      is NondetLabel ->
        copy(labels = labels.map { it.changeSubexpr(exprLut, parseContext) }.toSet())

      is SequenceLabel -> copy(labels = labels.map { it.changeSubexpr(exprLut, parseContext) })

      is StartLabel ->
        copy(
          params = params.map { it.changeSubexpr(exprLut, parseContext) },
          pidVar = pidVar.changeSubexpr(exprLut),
        )

      is StmtLabel -> copy(stmt = stmt.changeSubexpr(exprLut, parseContext))

      is ReturnLabel -> copy(enclosedLabel = enclosedLabel.changeSubexpr(exprLut))

      is FenceLabel -> {
        when (this) {
          is MutexLockLabel -> copy(handle = handle.changeSubexpr(exprLut))
          is MutexTryLockLabel ->
            copy(
              handle = handle.changeSubexpr(exprLut),
              successVar = successVar.changeSubexpr(exprLut),
            )

          is MutexUnlockLabel -> copy(handle = handle.changeSubexpr(exprLut))
          is RWLockReadLockLabel -> copy(handle = handle.changeSubexpr(exprLut))
          is RWLockWriteLockLabel -> copy(handle = handle.changeSubexpr(exprLut))
          is RWLockUnlockLabel -> copy(handle = handle.changeSubexpr(exprLut))
          else -> this
        }
      }

      else -> this
    }
  } else this

@JvmOverloads
fun Stmt.changeSubexpr(exprLut: Map<Expr<*>, Expr<*>>, parseContext: ParseContext? = null): Stmt {
  val stmt =
    when (this) {
      is AssignStmt<*> ->
        AssignStmt.of(
          cast(varDecl.changeSubexpr(exprLut), varDecl.type),
          cast(expr.changeSubexpr(exprLut, parseContext), varDecl.type),
        )

      is MemoryAssignStmt<*, *, *> ->
        MemoryAssignStmt.create(
          deref.changeSubexpr(exprLut) as Dereference<out Type, *, *>,
          expr.changeSubexpr(exprLut),
        )

      is HavocStmt<*> -> HavocStmt.of(varDecl.changeSubexpr(exprLut))
      is AssumeStmt -> AssumeStmt.of(cond.changeSubexpr(exprLut, parseContext))
      is SequenceStmt -> SequenceStmt.of(stmts.map { it.changeSubexpr(exprLut, parseContext) })
      is SkipStmt -> this
      else -> TODO("Not yet implemented")
    }
  val metadataValue = parseContext?.getMetadata()?.getMetadataValue(this, "sourceStatement")
  if (metadataValue?.isPresent == true)
    parseContext.getMetadata().create(stmt, "sourceStatement", metadataValue.get())
  return stmt
}

@JvmOverloads
fun <T : Type> Expr<T>.changeSubexpr(
  exprLut: Map<Expr<*>, Expr<*>>,
  parseContext: ParseContext? = null,
): Expr<T> {
  val ret = ExprUtils.changeSubexpr(this, exprLut)
  if (parseContext?.metadata?.getMetadataValue(this, "cType")?.isPresent == true) {
    parseContext.metadata?.create(ret, "cType", CComplexType.getType(this, parseContext))
  }
  return ret
}

fun <T : Type> VarDecl<T>.changeSubexpr(exprLut: Map<Expr<*>, Expr<*>>): VarDecl<T> {
  val changed = ExprUtils.changeSubexpr(this.ref, exprLut)
  return if (changed is RefExpr<*>) (changed.decl as VarDecl<T>) else this
}

fun XcfaProcedureBuilder.canInline(): Boolean = canInline(LinkedList())

private fun XcfaProcedureBuilder.canInline(tally: LinkedList<String>): Boolean {
  if (metaData["recursive"] != null) return false
  if (metaData["canInline"] != null) return true

  tally.push(name)
  val recursive =
    getEdges()
      .asSequence()
      .map { it.getFlatLabels() }
      .flatten()
      .filterIsInstance<InvokeLabel>()
      .mapNotNull { parent.getProcedures().find { proc -> proc.name == it.name } }
      .any { tally.contains(it.name) || !it.canInline(tally) }
  tally.pop()
  metaData[if (recursive) "recursive" else "canInline"] = Unit
  return !recursive
}

fun combineMetadata(vararg metaData: MetaData): MetaData = combineMetadata(metaData.toList())

fun combineMetadata(metaData: Collection<MetaData>): MetaData =
  metaData.reduce { i1, i2 -> i1.combine(i2) }

/**
 * Find loop locations and edges starting from the loop head. The loop head is the target of the
 * given backward edge.
 */
fun getLoopElements(backEdge: XcfaEdge): Pair<Set<XcfaLocation>, Set<XcfaEdge>> {
  val loopStart = backEdge.target
  val backSearch: (XcfaLocation) -> Pair<Set<XcfaLocation>, List<XcfaEdge>>? =
    backSearch@{ startLoc ->
      val locs = mutableSetOf<XcfaLocation>()
      val edges = mutableListOf<XcfaEdge>()
      val toVisit = mutableListOf(startLoc)
      while (toVisit.isNotEmpty()) {
        val current = toVisit.removeFirst()
        if (current == loopStart) continue
        if (current.incomingEdges.isEmpty()) return@backSearch null // not part of the loop
        if (locs.add(current)) {
          edges.addAll(current.incomingEdges)
          toVisit.addAll(current.incomingEdges.map { it.source })
        }
      }
      locs to edges
    }

  val locs = mutableSetOf(loopStart)
  val edges = mutableSetOf<XcfaEdge>()
  val nonLoopEdge =
    loopStart.incomingEdges.filter { it != backEdge }.let { if (it.size != 1) null else it.first() }
  loopStart.incomingEdges.forEach { incoming ->
    if (incoming == nonLoopEdge) return@forEach
    val (l, e) = backSearch(incoming.source) ?: return@forEach
    locs.addAll(l)
    edges.addAll(e)
    edges.add(incoming)
  }
  return locs to edges
}

private fun getLoopEdges(initLoc: XcfaLocation): Set<XcfaEdge> {
  val loopEdges = mutableSetOf<XcfaEdge>()
  val visited = mutableSetOf<XcfaEdge>()
  val stack = Stack<XcfaLocation>()
  stack.push(initLoc)
  while (stack.isNotEmpty()) {
    val loc = stack.peek()
    val edge = loc.outgoingEdges.firstOrNull { it !in visited }
    if (edge == null) {
      stack.pop()
      continue
    }
    visited.add(edge)
    if (edge.target in stack) {
      val (_, edges) = getLoopElements(edge)
      loopEdges.addAll(edges)
    } else {
      stack.push(edge.target)
    }
  }
  return loopEdges
}

val XcfaProcedureBuilder.loopEdges: Set<XcfaEdge>
  get() = getLoopEdges(initLoc)

val XcfaProcedure.loopEdges: Set<XcfaEdge>
  get() = getLoopEdges(initLoc)
