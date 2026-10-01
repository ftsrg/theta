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
import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceChecker
import hu.bme.mit.theta.analysis.expr.refinement.Refutation
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.analysis.ptr.repatch
import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.abstracttype.NeqExpr
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.PathUtils
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.solver.Solver
import hu.bme.mit.theta.solver.UnknownSolverStatusException
import hu.bme.mit.theta.solver.utils.WithPushPop
import hu.bme.mit.theta.solver.z3.Z3SolverFactory
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.passes.changeVars
import hu.bme.mit.theta.xcfa.utils.*

private val dependencySolver: Solver by lazy { Z3SolverFactory.getInstance().createSolver() }

/** One of the two conflicting accesses of a data race. */
data class DataRaceAccess(val pid: Int, val edge: XcfaEdge, val label: XcfaLabel)

/**
 * A pair of conflicting accesses constituting a data race. [condition] is the extra path condition
 * under which the two accesses actually alias -- the aliasing condition for memory accesses, [True]
 * for a plain global-variable race.
 */
data class DataRace(
  val access1: DataRaceAccess,
  val access2: DataRaceAccess,
  val condition: Expr<BoolType>,
)

/**
 * Finds a pair of conflicting accesses (same location, different processes, at least one write, not
 * both atomic, not mutually excluded) enabled after [s], or null if no data race is possible.
 *
 * The returned [DataRace] carries the racing edges and labels the concurrent-witness writer needs;
 * [getDataRaceDetector] and the trace-checker wrapper only look at [DataRace.condition]. `_Atomic`
 * accesses are excluded here (via [parseContext]), so both consumers stay atomic-aware.
 */
fun findDataRace(s: XcfaState<out PtrState<out ExprState>>, parseContext: ParseContext): DataRace? {
  if (s.isBottom) return null
  val xcfa = s.xcfa!!
  val processes = s.processes.entries.toList()
  for (i in processes.indices) {
    val process1 = processes[i]
    for (j in i + 1 until processes.size) {
      val process2 = processes[j]
      check(process1.key != process2.key)
      for (edge1 in process1.value.locs.peek().outgoingEdges) {
        for (edge2 in process2.value.locs.peek().outgoingEdges) {
          val label1 = edge1.label.changeVars(process1.value.varLookup.peek())
          val label2 = edge2.label.changeVars(process2.value.varLookup.peek())
          val mutexes1 = s.mutexes.filterValues { process1.key in it }.keys
          val mutexes2 = s.mutexes.filterValues { process2.key in it }.keys

          val globals1 = label1.getGlobalVarsWithNeededMutexes(xcfa, mutexes1, s)
          val globals2 = label2.getGlobalVarsWithNeededMutexes(xcfa, mutexes2, s)
          for (v1 in globals1) {
            for (v2 in globals2) {
              if (
                v1.globalVar == v2.globalVar &&
                  !v1.globalVar.atomic &&
                  (v1.access.isWritten || v2.access.isWritten) &&
                  mayExecuteConcurrently(v1, v2)
              )
                return DataRace(
                  DataRaceAccess(process1.key, edge1, v1.label),
                  DataRaceAccess(process2.key, edge2, v2.label),
                  And(concurrentExecutionCondition(v1, v2), v1.precondition, v2.precondition),
                )
            }
          }

          val mems1 = label1.getMemoryAccessesWithMutexes(mutexes1, xcfa, parseContext, s)
          val mems2 = label2.getMemoryAccessesWithMutexes(mutexes2, xcfa, parseContext, s)
          for (m1 in mems1) {
            for (m2 in mems2) {
              if (
                (m1.access.isWritten || m2.access.isWritten) &&
                  !m1.atomic &&
                  !m2.atomic &&
                  mayExecuteConcurrently(m1, m2) &&
                  mayBeSameMemoryLocation(m1, m2, s)
              ) {
                return DataRace(
                  DataRaceAccess(process1.key, edge1, m1.label),
                  DataRaceAccess(process2.key, edge2, m2.label),
                  And(
                    concurrentExecutionCondition(m1, m2),
                    m1.precondition,
                    m2.precondition,
                    Eq(m1.array, m2.array),
                    Eq(m1.offset, m2.offset),
                  ),
                )
              }
            }
          }
        }
      }
    }
  }
  return null
}

/** Returns a predicate that checks whether data race is possible after the given state. */
fun getDataRaceDetector(parseContext: ParseContext) =
  object : XcfaErrorDetector {

    override fun test(s: XcfaState<out PtrState<out ExprState>>): Boolean =
      findDataRace(s, parseContext) != null

    override fun <T : Refutation> exprTraceCheckerWrapper(
      exprTraceChecker: ExprTraceChecker<T>
    ): ExprTraceChecker<T> =
      wrapExprTraceCheckerWithDataRaceCondition(exprTraceChecker, parseContext)
  }

/**
 * Wraps [exprTraceChecker] so that, before it checks a trace, the aliasing condition of the data
 * race enabled in the trace's last state is asserted on the last action -- turning a "the accesses
 * *may* alias" abstraction into the concrete race the refinement must respect.
 */
fun <T : Refutation> wrapExprTraceCheckerWithDataRaceCondition(
  exprTraceChecker: ExprTraceChecker<T>,
  parseContext: ParseContext,
): ExprTraceChecker<T> = ExprTraceChecker { trace ->
  val t =
    if (
      trace.states.isEmpty() ||
        trace.actions.isEmpty() ||
        trace.states.last() !is XcfaState<*> ||
        trace.actions.last() !is XcfaAction
    ) {
      trace
    } else {
      val lastState = trace.states.last() as XcfaState<out PtrState<out ExprState>>
      findDataRace(lastState, parseContext)?.condition?.let { extraAssumption ->
        Trace.of(
          trace.states,
          trace.actions.subList(0, trace.actions.size - 1) +
            trace.actions.last().let {
              (it as XcfaAction).withLabel(
                SequenceLabel(listOf(it.label, StmtLabel(AssumeStmt.of(extraAssumption))))
              )
            },
        )
      } ?: trace
    }
  exprTraceChecker.check(t)
}

/** Applies [wrapExprTraceCheckerWithDataRaceCondition] only when the property is a data race. */
fun <T : Refutation> wrapExprTraceCheckerWithDataRaceCondition(
  property: XcfaProperty?,
  parseContext: ParseContext,
): (ExprTraceChecker<T>) -> ExprTraceChecker<T> =
  if (property?.verifiedProperty == ErrorDetection.DATA_RACE) {
    { wrapExprTraceCheckerWithDataRaceCondition(it, parseContext) }
  } else {
    { it }
  }

private sealed class GlobalAccessWithMutexes(
  /** The (flat) label the access was found in -- the concurrent-witness writer reports it. */
  val label: XcfaLabel,
  val access: AccessType,
  val acquiredMutexes: Set<MutexLock>,
  val blockingMutexes: Set<MutexLock>,
  val precedingAssumes: List<AssumeStmt>,
) {
  val precondition: Expr<BoolType>
    get() =
      precedingAssumes.fold<AssumeStmt, Expr<BoolType>>(True()) { acc, assume ->
        And(acc, assume.cond)
      }
}

/**
 * Represents a global variable access: stores the variable declaration, the access type
 * (read/write) and the set of acquired/blocking mutexes for performing the variable access.
 */
private class GlobalVarAccessWithMutexes(
  val globalVar: XcfaGlobalVar,
  label: XcfaLabel,
  access: AccessType,
  acquiredMutexes: Set<MutexLock>,
  blockingMutexes: Set<MutexLock>,
  precedingAssumes: List<AssumeStmt>,
) : GlobalAccessWithMutexes(label, access, acquiredMutexes, blockingMutexes, precedingAssumes)

/**
 * Represents a memory access: stores the array expression, the offset expression, the access type
 * (read/write) and the set of acquired/blocking mutexes for performing the variable access.
 */
private class MemoryAccessWithMutexes(
  label: XcfaLabel,
  val array: Expr<*>,
  val offset: Expr<*>,
  /** The cell is `_Atomic`, so nothing that touches it races with anything. */
  val atomic: Boolean,
  /**
   * The address reads memory after an earlier memory write of the same label, so it cannot be
   * evaluated in the state before the label.
   */
  val addressAfterMemoryWrite: Boolean,
  access: AccessType,
  acquiredMutexes: Set<MutexLock>,
  blockingMutexes: Set<MutexLock>,
  precedingAssumes: List<AssumeStmt>,
) : GlobalAccessWithMutexes(label, access, acquiredMutexes, blockingMutexes, precedingAssumes)

/**
 * Returns the global variable accesses of the label.
 *
 * @param xcfa the XCFA that contains the label
 * @param currentMutexes the set of mutexes currently acquired by the process of the label
 * @return the list of global variable accesses (c.f., [GlobalVarAccessWithMutexes])
 */
private fun XcfaLabel.getGlobalVarsWithNeededMutexes(
  xcfa: XCFA,
  currentMutexes: Set<MutexLock>,
  state: State,
): List<GlobalVarAccessWithMutexes> {
  val globalVars = xcfa.globalVars
  val acquiredMutexes = currentMutexes.toMutableSet()
  val blockingMutexes = mutableSetOf<MutexLock>()
  val accesses = mutableListOf<GlobalVarAccessWithMutexes>()
  val precedingAssumes = mutableListOf<AssumeStmt>()
  getFlatLabels().forEach { label ->
    if (label is FenceLabel) {
      acquiredMutexes.addAll(label.acquiredMutexes(state))
      blockingMutexes.addAll(label.blockingMutexes(state))
    } else {
      label.collectGlobalVars(globalVars).forEach { (v, access) ->
        if (accesses.none { it.globalVar == v && (it.access == access && it.access == WRITE) }) {
          accesses.add(
            GlobalVarAccessWithMutexes(
              v,
              label,
              access,
              acquiredMutexes.toSet(),
              blockingMutexes.toSet(),
              precedingAssumes.toList(),
            )
          )
        }
      }
    }

    ((label as? StmtLabel)?.stmt as? AssumeStmt)?.let(precedingAssumes::add)
  }
  return accesses
}

/**
 * Returns the memory accesses of the label.
 *
 * @param currentMutexes the set of mutexes currently acquired by the process of the label
 * @return the list of memory accesses (c.f., [MemoryAccessWithMutexes])
 */
private fun XcfaLabel.getMemoryAccessesWithMutexes(
  currentMutexes: Set<MutexLock>,
  xcfa: XCFA,
  parseContext: ParseContext,
  state: State,
): List<MemoryAccessWithMutexes> {
  val acquiredMutexes = currentMutexes.toMutableSet()
  val blockingMutexes = mutableSetOf<MutexLock>()
  val accesses = mutableListOf<MemoryAccessWithMutexes>()
  val changedVars = mutableSetOf<VarDecl<*>>()
  val precedingAssumes = mutableListOf<AssumeStmt>()
  var memoryWritten = false
  getFlatLabels().forEach { label ->
    if (label is FenceLabel) {
      acquiredMutexes.addAll(label.acquiredMutexes(state))
      blockingMutexes.addAll(label.blockingMutexes(state))
    } else {
      val derefs = label.dereferencesWithAccessType
      derefs.forEach { (deref, access) ->
        val vars = ExprUtils.getVars(deref.array) + ExprUtils.getVars(deref.offset)
        check(changedVars.intersect(vars).isEmpty()) {
          "Cannot handle dereferences with changed variables in between: $this"
        }
        val addressAfterMemoryWrite =
          memoryWritten &&
            (deref.array.dereferences.isNotEmpty() || deref.offset.dereferences.isNotEmpty())
        if (
          addressAfterMemoryWrite ||
            accesses.none {
              it.array == deref.array &&
                it.offset == deref.offset &&
                (it.access == access && it.access == WRITE)
            }
        ) {
          accesses.add(
            MemoryAccessWithMutexes(
              label,
              deref.array,
              deref.offset,
              deref.addressesAtomicData(xcfa.globalVars, parseContext),
              addressAfterMemoryWrite,
              access,
              acquiredMutexes.toSet(),
              blockingMutexes.toSet(),
              precedingAssumes.toList(),
            )
          )
        }
      }
      if (derefs.values.any { it.isWritten }) memoryWritten = true
    }
    ((label as? StmtLabel)?.stmt as? AssumeStmt)?.let(precedingAssumes::add)
    label.collectVarsWithAccessType().forEach { (v, access) ->
      if (access.isWritten) changedVars.add(v)
    }
  }
  return accesses
}

/**
 * Checks whether the locations of the two given memory accesses may be the same under the given
 * state.
 *
 * @param access1 the first memory access
 * @param access2 the second memory access
 * @param state the state to check under
 * @return true if the two memory locations may be the same, false otherwise
 */
private fun mayBeSameMemoryLocation(
  access1: MemoryAccessWithMutexes,
  access2: MemoryAccessWithMutexes,
  state: XcfaState<out PtrState<out ExprState>>,
): Boolean {
  val possibleSameLocation =
    access1.addressAfterMemoryWrite ||
      access2.addressAfterMemoryWrite ||
      mayBeSameAddress(access1, access2, state)
  if (!possibleSameLocation) return false

  val pointerPartitions = state.xcfa!!.getPointerPartitions()
  val a1 = (access1.array as? RefExpr<*>)?.decl ?: return true // cannot decide
  val a2 = (access2.array as? RefExpr<*>)?.decl ?: return true // cannot decide
  val partition1 = pointerPartitions.indexOfFirst { a1.belongsTo(it, state) }
  val partition2 = pointerPartitions.indexOfFirst { a2.belongsTo(it, state) }
  if (partition1 == -1 || partition2 == -1) return true // cannot decide
  return partition1 == partition2
}

/**
 * Asks the solver whether the addresses of the two accesses may coincide in [state]. Nested
 * dereferences in the addresses read the current memory contents, which abstract states name by
 * uniqueness index 0 (see `repatch`). The state is repatched too: the refiner hands over patched
 * ones.
 */
private fun mayBeSameAddress(
  access1: MemoryAccessWithMutexes,
  access2: MemoryAccessWithMutexes,
  state: XcfaState<out PtrState<out ExprState>>,
): Boolean {
  var expr: Expr<BoolType> =
    And(Eq(access1.array, access2.array), Eq(access1.offset, access2.offset))
  expr =
    (state.sGlobal.innerState as? ExplState)?.let { s -> ExprUtils.simplify(expr, s.`val`) }
      ?: ExprUtils.simplify(expr)
  return try {
    WithPushPop(dependencySolver).use {
      dependencySolver.add(PathUtils.unfold(state.sGlobal.innerState.repatch().toExpr(), 0))
      dependencySolver.add(PathUtils.unfold(expr.readingCurrentMemory(), 0))
      dependencySolver.check().isSat
    }
  } catch (_: UnknownSolverStatusException) {
    true
  }
}

private fun <T : Type> Expr<T>.readingCurrentMemory(): Expr<T> =
  when (this) {
    is Dereference<*, *, T> -> withUniquenessExpr(Int(0)).map { it.readingCurrentMemory() }
    else -> map { it.readingCurrentMemory() }
  }

private fun Decl<*>.belongsTo(
  partition: Pair<Set<VarDecl<*>>, Set<LitExpr<*>>>,
  state: XcfaState<*>,
): Boolean {
  if (this in partition.first) return true
  for ((_, procState) in state.processes) {
    for (lookUp in procState.varLookup) {
      for ((original, prefixed) in lookUp) {
        if (prefixed == this) {
          return original in partition.first
        }
      }
    }
  }
  return false
}

private fun mayExecuteConcurrently(
  access1: GlobalAccessWithMutexes,
  access2: GlobalAccessWithMutexes,
): Boolean =
  (access1.acquiredMutexes intersect access2.blockingMutexes).isEmpty() &&
    (access2.acquiredMutexes intersect access1.blockingMutexes).isEmpty()

private fun concurrentExecutionCondition(
  access1: GlobalAccessWithMutexes,
  access2: GlobalAccessWithMutexes,
): Expr<BoolType> =
  And(
    noCommon(access1.acquiredMutexes, access2.blockingMutexes),
    noCommon(access2.acquiredMutexes, access1.blockingMutexes),
  )

private fun noCommon(mutexes1: Set<MutexLock>, mutexes2: Set<MutexLock>): Expr<BoolType> =
  And(
    mutexes1.flatMap { m1 ->
      mutexes2.mapNotNull { m2 ->
        if (!m1.isKnown() || !m2.isKnown()) NeqExpr.create2(m1.lock, m2.lock) else null
      }
    }
  )
