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
@file:JvmName("Traceability")

package hu.bme.mit.theta.core.type

import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.ForeignStmt
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.core.stmt.IfStmt
import hu.bme.mit.theta.core.stmt.LoopStmt
import hu.bme.mit.theta.core.stmt.MemoryAssignStmt
import hu.bme.mit.theta.core.stmt.NonDetStmt
import hu.bme.mit.theta.core.stmt.OrtStmt
import hu.bme.mit.theta.core.stmt.SequenceStmt
import hu.bme.mit.theta.core.stmt.SkipStmt
import hu.bme.mit.theta.core.stmt.Stmt
import java.util.IdentityHashMap

/** This expression without its outermost [TraceableWrapperExpr]s. */
fun <ExprType : Type> Expr<ExprType>.unwrapTraceable(): Expr<ExprType> {
  var e = this
  while (e is TraceableWrapperExpr<ExprType>) e = e.expr
  return e
}

/** The info of the outermost wrapper of this expression, if it is wrapped. */
val Expr<*>.traceabilityInfo: TraceabilityInfo?
  get() = (this as? TraceableWrapperExpr<*>)?.info

/** Whether this expression contains a [TraceableWrapperExpr] anywhere. */
fun Expr<*>.containsTraceability(): Boolean {
  if (this is TraceableWrapperExpr<*>) return true
  if (arity == 0) return false
  // Expressions are DAGs: visit shared subexpressions once.
  val visited = java.util.Collections.newSetFromMap(IdentityHashMap<Expr<*>, Boolean>())
  val stack = ArrayDeque<Expr<*>>()
  stack.add(this)
  while (stack.isNotEmpty()) {
    val e = stack.removeLast()
    if (e is TraceableWrapperExpr<*>) return true
    if (visited.add(e))
      e.ops.forEach { if (it.arity > 0 || it is TraceableWrapperExpr<*>) stack.add(it) }
  }
  return false
}

/**
 * This expression with every [TraceableWrapperExpr] removed. Subexpressions without wrappers are
 * kept as they are (by identity). If [infos] is given, it receives the info of every node that was
 * wrapped, keyed by the identity of the node in the result.
 */
@JvmOverloads
fun <ExprType : Type> Expr<ExprType>.stripTraceability(
  infos: MutableMap<Expr<*>, TraceabilityInfo>? = null
): Expr<ExprType> {
  @Suppress("UNCHECKED_CAST") return Stripper(infos).strip(this) as Expr<ExprType>
}

/**
 * Wraps every node of this expression that is a key of [infos] (by identity) with its info; the
 * inverse of [stripTraceability] for the nodes an operation left unchanged.
 */
fun <ExprType : Type> Expr<ExprType>.rewrapTraceability(
  infos: Map<Expr<*>, TraceabilityInfo>
): Expr<ExprType> {
  if (infos.isEmpty()) return this
  @Suppress("UNCHECKED_CAST") return Rewrapper(infos).rewrap(this) as Expr<ExprType>
}

/** This statement with every [TraceableWrapperExpr] removed; itself if it contains none. */
fun Stmt.stripTraceability(): Stmt =
  when (this) {
    is AssignStmt<*> ->
      expr.bare().let { if (it === expr) this else AssignStmt.create<Type>(varDecl, it) }
    is AssumeStmt -> cond.bare().let { if (it === cond) this else AssumeStmt.of(it) }
    is MemoryAssignStmt<*, *, *> -> {
      val newDeref = deref.bare()
      val newExpr = expr.bare()
      if (newDeref === tracedDeref && newExpr === expr) this
      else MemoryAssignStmt.create(newDeref, newExpr)
    }
    is SequenceStmt -> stmts.stripEach()?.let { SequenceStmt.of(it) } ?: this
    is NonDetStmt -> stmts.stripEach()?.let { NonDetStmt.of(it) } ?: this
    is OrtStmt -> stmts.stripEach()?.let { OrtStmt.of(it) } ?: this
    is IfStmt -> {
      val newCond = cond.bare()
      val newThen = then.stripTraceability()
      val newElze = elze.stripTraceability()
      if (newCond === cond && newThen === then && newElze === elze) this
      else IfStmt.of(newCond, newThen, newElze)
    }
    is LoopStmt -> {
      val newStmt = stmt.stripTraceability()
      val newFrom = from.bare()
      val newTo = to.bare()
      if (newStmt === stmt && newFrom === from && newTo === to) this
      else LoopStmt.of(newStmt, loopVariable, newFrom, newTo)
    }
    is HavocStmt<*>,
    is SkipStmt,
    is ForeignStmt -> this
  }

private fun <T : Type> Expr<T>.bare(): Expr<T> =
  if (containsTraceability()) stripTraceability() else this

/** The stripped statements, or null if none of them changed. */
private fun List<Stmt>.stripEach(): List<Stmt>? {
  val stripped = map { it.stripTraceability() }
  return if (stripped.indices.all { stripped[it] === this[it] }) null else stripped
}

private class Stripper(private val infos: MutableMap<Expr<*>, TraceabilityInfo>?) {
  private val done = IdentityHashMap<Expr<*>, Expr<*>>()

  fun strip(e: Expr<*>): Expr<*> =
    done[e]
      ?: run {
        val result =
          if (e is TraceableWrapperExpr<*>) {
            strip(e.expr).also { infos?.put(it, e.info) }
          } else {
            val ops = e.ops
            val newOps = ops.map { strip(it) }
            if (newOps.indices.all { newOps[it] === ops[it] }) e else e.withOps(newOps)
          }
        done[e] = result
        result
      }
}

private class Rewrapper(private val infos: Map<Expr<*>, TraceabilityInfo>) {
  private val done = IdentityHashMap<Expr<*>, Expr<*>>()

  fun rewrap(e: Expr<*>): Expr<*> =
    done[e]
      ?: run {
        val ops = e.ops
        val newOps = ops.map { rewrap(it) }
        val rebuilt = if (newOps.indices.all { newOps[it] === ops[it] }) e else e.withOps(newOps)
        val result = infos[e]?.let { TraceableWrapperExpr.of(rebuilt, it) } ?: rebuilt
        done[e] = result
        result
      }
}
