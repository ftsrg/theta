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
package hu.bme.mit.theta.xcfa.passes

import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.Stmts.Havoc
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.*
import hu.bme.mit.theta.core.type.anytype.Exprs
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.anytype.Reference
import hu.bme.mit.theta.core.type.booltype.BoolExprs.*
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.UnsupportedFrontendElementException
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.AssignStmtLabel
import java.util.*

/**
 * Models POSIX barriers, so that `pthread_barrier_wait` blocks until `count` threads have reached
 * the barrier, instead of being havoced into a no-op.
 *
 * Each barrier gets four atomic globals: its `count`, the number of threads `arrived`, `draining`
 * (the barrier has tripped and its waiters are leaving) and `claimed` (one of them has taken
 * `PTHREAD_BARRIER_SERIAL_THREAD`). A wait is two atomic steps: arriving, which trips the barrier
 * as the `count`th arrival, and departing, which is blocked until it has tripped. Arrivals of the
 * next round are held back until the current waiters have left; that loses no behavior, as a
 * departure changes nothing but the barrier and can always be moved to the instant it tripped.
 * Which waiter receives the serial value is nondeterministic, as POSIX leaves it unspecified.
 *
 * Only a barrier named by the address of a global variable is supported. One behind a pointer, a
 * member or an array element has no static identity here, so it is refused.
 */
private val BARRIERS = WeakHashMap<XcfaBuilder, MutableMap<VarDecl<*>, Barrier>>()

class PthreadBarrierPass(val parseContext: ParseContext) : ProcedurePass {

  private companion object {
    val FUNCTIONS =
      setOf(
        "pthread_barrier_init",
        "pthread_barrier_wait",
        "pthread_barrier_destroy",
        "pthread_barrierattr_init",
        "pthread_barrierattr_destroy",
        "pthread_barrierattr_setpshared",
      )

    /** glibc's `EINVAL`, returned for a barrier of count zero. */
    const val EINVAL = 22
  }

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    val defined = builder.parent.getProcedures().map { it.name }.toSet()
    val predicate = { label: XcfaLabel ->
      label is InvokeLabel && label.name in FUNCTIONS && label.name !in defined
    }
    for (edge in ArrayList(builder.getEdges())) {
      val edges = edge.splitIf(predicate)
      if (edges.none { predicate((it.label as SequenceLabel).labels[0]) }) continue
      builder.removeEdge(edge)
      for (e in edges) {
        val invoke = (e.label as SequenceLabel).labels[0]
        if (!predicate(invoke)) {
          builder.addEdge(e)
          continue
        }
        invoke as InvokeLabel
        val ret = invoke.params[0]
        val retType = CComplexType.getType(ret, parseContext)
        val assignRet = { value: Expr<*> -> AssignStmtLabel(ret, value, invoke.metadata) }
        when (invoke.name) {
          "pthread_barrier_init" -> {
            val barrier = barrierOf(builder, invoke)
            val count = barrier.uint.castTo(invoke.params[3])
            val invalid = Eq(count, barrier.uint.nullValue)
            val labels =
              listOf(
                assignRet(Ite<Type>(invalid, retType.getValue("$EINVAL"), retType.nullValue)),
                assign(barrier.count, count),
              ) + barrier.reset()
            builder.addEdge(e.withLabel(SequenceLabel(labels, invoke.metadata)))
          }

          "pthread_barrier_wait" -> {
            val barrier = barrierOf(builder, invoke)
            val mid =
              XcfaLocation(
                "${e.source.name}_barrier${XcfaLocation.uniqueCounter()}",
                metadata = e.source.metadata,
              )
            builder.addEdge(XcfaEdge(e.source, mid, SequenceLabel(barrier.arrive()), e.metadata))
            val serial = Var("__theta_barrier_serial_${XcfaLocation.uniqueCounter()}", Bool())
            builder.addVar(serial)
            val departureLabel = SequenceLabel(barrier.departures(assignRet, retType, serial))
            builder.addEdge(XcfaEdge(mid, e.target, departureLabel, e.metadata))
          }

          // Process sharing only matters across `fork`, which is never modeled (see
          // UnresolvedInvokeToHavocPass); destroying a barrier no one waits on has no effect.
          else -> {
            if (invoke.name == "pthread_barrier_destroy") barrierOf(builder, invoke)
            builder.addEdge(e.withLabel(SequenceLabel(listOf(assignRet(retType.nullValue)))))
          }
        }
      }
    }
    return builder
  }

  private fun barrierOf(builder: XcfaProcedureBuilder, invoke: InvokeLabel): Barrier {
    val handle = invoke.params.getOrNull(1)
    val decl = ((handle as? Reference<*, *>)?.expr as? RefExpr<*>)?.decl as? VarDecl<*>
    if (decl == null || builder.parent.getVars().none { it.wrappedVar == decl }) {
      throw UnsupportedFrontendElementException(
        "Unsupported barrier ${handle}: only the address of a global barrier variable is supported."
      )
    }
    parseContext.metadata.create(decl, CLibraryFunctionsPass.SYNC_VAR_METADATA_KEY, true)
    // Passes are instantiated per procedure, so the model of a barrier is kept per XCFA.
    val barriers = synchronized(BARRIERS) { BARRIERS.getOrPut(builder.parent) { LinkedHashMap() } }
    return synchronized(barriers) {
      barriers.getOrPut(decl) {
        Barrier(builder.parent, "${decl.name}_${barriers.size}", parseContext)
      }
    }
  }
}

private class Barrier(xcfa: XcfaBuilder, name: String, parseContext: ParseContext) {
  val uint: CComplexType = CComplexType.getUnsignedInt(parseContext)
  val count = global(xcfa, "__theta_barrier_count_$name", uint.smtType, uint.nullValue)
  val arrived = global(xcfa, "__theta_barrier_arrived_$name", uint.smtType, uint.nullValue)
  val draining = global(xcfa, "__theta_barrier_draining_$name", Bool(), False())
  val claimed = global(xcfa, "__theta_barrier_claimed_$name", Bool(), False())

  private val zero = uint.nullValue
  private val one = uint.getValue("1")

  fun reset(): List<XcfaLabel> =
    listOf(assign(arrived, zero), assign(draining, False()), assign(claimed, False()))

  /** Joins the current round, tripping the barrier as its last arrival. */
  fun arrive(): List<XcfaLabel> =
    listOf(
      assume(Not(draining.ref)),
      assign(arrived, Add(arrived.ref, one)),
      assign(draining, Eq(arrived.ref, count.ref)),
    )

  /**
   * Leaving a tripped barrier: as the serial thread, or as any other, which the last waiter to
   * leave may only be when the serial value is already taken.
   */
  fun departures(
    assignRet: (Expr<*>) -> StmtLabel,
    retType: CComplexType,
    serial: VarDecl<BoolType>,
  ): List<XcfaLabel> {
    val othersRemain = Neq(arrived.ref, zero)
    val serialValue = retType.getValue("-1")
    val otherValue = retType.nullValue
    return listOf(
      assume(draining.ref),
      StmtLabel(Havoc(serial)),
      assume(
        Or(
          And(serial.ref, Not(claimed.ref)),
          And(Not(serial.ref), Or(claimed.ref, Neq(arrived.ref, one))),
        )
      ),
      assignRet(
        Exprs.Ite(
          serial.ref,
          cast(serialValue, serialValue.type),
          cast(otherValue, serialValue.type),
        )
      ),
      assign(arrived, Sub(arrived.ref, one)),
      assign(claimed, And(Or(claimed.ref, serial.ref), othersRemain)),
      assign(draining, othersRemain),
    )
  }
}

private fun <T : Type> global(
  xcfa: XcfaBuilder,
  name: String,
  type: T,
  init: LitExpr<*>,
): VarDecl<T> {
  val v = Var(name, type)
  xcfa.addVar(XcfaGlobalVar(v, init, atomic = true))
  return v
}

private fun assign(v: VarDecl<*>, value: Expr<*>): XcfaLabel = AssignStmtLabel(v, value)

@Suppress("UNCHECKED_CAST")
private fun assume(cond: Expr<*>): XcfaLabel = StmtLabel(AssumeStmt.of(cond as Expr<BoolType>))
