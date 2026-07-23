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

import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceChecker
import hu.bme.mit.theta.analysis.expr.refinement.Refutation
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.core.utils.BvUtils
import java.math.BigInteger
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.PathUtils
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CArray
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CPointer
import hu.bme.mit.theta.solver.Solver
import hu.bme.mit.theta.solver.utils.WithPushPop
import hu.bme.mit.theta.solver.z3.Z3SolverFactory
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.passes.changeVars
import hu.bme.mit.theta.xcfa.utils.*

private val dependencySolver: Solver by lazy { Z3SolverFactory.getInstance().createSolver() }

/**
 * Whether the cell this dereference reads is `_Atomic` -- accesses to it are, by definition, not
 * data races with anything.
 *
 * A race between two *variables* checks whether the **variable** is atomic (`!v1.globalVar.atomic`,
 * below). An access *through* a dereference touches the cell it points **at**, which is a different
 * question, and `_Atomic` says which is which:
 * ```
 * _Atomic int *p;   // p is an ordinary variable; p[i] is atomic, and cannot be raced on
 * int * _Atomic p;  // p itself is atomic; what it points at is not
 * ```
 *
 * `_Atomic` is a property of the accessed *cell* -- a struct field, an array element, or a pointee --
 * but the expression that reaches it is a bare `(base, offset)` of literals by analysis time (folded
 * constants, rebuilt exprs, identity-keyed C types all lost). So atomicity is recorded against the
 * object's base id where that id is minted (global layout in the frontend builder, address-taken
 * objects in [ReferenceElimination]) and resolved here by the base id's *value*.
 *
 * A live pointer *variable* (not folded to a base) is still asked its type directly.
 *
 * Nothing found means nothing skipped -- reporting a race is the safe direction.
 */
private fun Dereference<*, *, *>.addressesAtomicData(
  xcfa: XCFA,
  parseContext: ParseContext,
): Boolean {
  // The object being accessed, identified by the base id its dereference resolves to.
  array.resolveObjectBase(parseContext)?.let { base ->
    if (parseContext.isAtomicObjectCell(base, offset.asConstantBigInteger()?.toInt())) return true
  }
  // A live pointer *variable*: its type says what it points at.
  (array as? RefExpr<*>)?.decl?.let { decl ->
    xcfa.globalVars
      .firstOrNull { it.wrappedVar == decl }
      ?.let { if (it.pointsToAtomic) return true }
    val pointee =
      try {
        when (val type = CComplexType.getType(array, parseContext)) {
          is CPointer -> type.embeddedType
          is CArray -> type.embeddedType
          else -> null
        }
      } catch (e: Exception) {
        null
      }
    if (pointee?.isAtomic == true) return true
  }
  // An address-taken object, whose pointer has been folded to a bare literal -- its object id. The
  // pointer ReferenceElimination invented for it still holds that id, and remembers what it points
  // at.
  return xcfa.globalVars.any { it.pointsToAtomic && it.initValue == array }
}

/** The value of a bare integer/bitvector literal, or null when this is not a compile-time constant. */
private fun Expr<*>.asConstantBigInteger(): BigInteger? =
  when (this) {
    is IntLitExpr -> value
    is BvLitExpr -> BvUtils.neutralBvLitExprToBigInteger(this)
    else -> null
  }

/**
 * The base id of the object this dereference-base expression denotes: a bare literal is that id
 * directly; a nested `(deref parent offset)` reads a subobject's base from its parent's cell, so it
 * resolves through [ParseContext.subObjectBaseAt] (recursively, for `s.a.b.c`).
 */
private fun Expr<*>.resolveObjectBase(parseContext: ParseContext): BigInteger? {
  asConstantBigInteger()?.let {
    return it
  }
  if (this is Dereference<*, *, *>) {
    val parent = array.resolveObjectBase(parseContext) ?: return null
    val offsetValue = offset.asConstantBigInteger()?.toInt() ?: return null
    return parseContext.subObjectBaseAt(parent, offsetValue)
  }
  return null
}

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

          val globals1 = label1.getGlobalVarsWithNeededMutexes(xcfa, mutexes1)
          val globals2 = label2.getGlobalVarsWithNeededMutexes(xcfa, mutexes2)
          for (v1 in globals1) {
            for (v2 in globals2) {
              if (
                v1.globalVar == v2.globalVar &&
                  !v1.globalVar.atomic &&
                  (v1.access.isWritten || v2.access.isWritten) &&
                  canExecuteConcurrently(v1, v2)
              )
                return DataRace(
                  DataRaceAccess(process1.key, edge1, v1.label),
                  DataRaceAccess(process2.key, edge2, v2.label),
                  True(),
                )
            }
          }

          val mems1 = label1.getMemoryAccessesWithMutexes(mutexes1, xcfa, parseContext)
          val mems2 = label2.getMemoryAccessesWithMutexes(mutexes2, xcfa, parseContext)
          for (m1 in mems1) {
            for (m2 in mems2) {
              if (
                (m1.access.isWritten || m2.access.isWritten) &&
                  !m1.atomic &&
                  !m2.atomic &&
                  canExecuteConcurrently(m1, m2) &&
                  mayBeSameMemoryLocation(m1.array, m1.offset, m2.array, m2.offset, s)
              ) {
                return DataRace(
                  DataRaceAccess(process1.key, edge1, m1.label),
                  DataRaceAccess(process2.key, edge2, m2.label),
                  And(Eq(m1.array, m2.array), Eq(m1.offset, m2.offset)),
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
  val acquiredMutexes: Set<String>,
  val blockingMutexes: Set<String>,
)

/**
 * Represents a global variable access: stores the variable declaration, the access type
 * (read/write) and the set of acquired/blocking mutexes for performing the variable access.
 */
private class GlobalVarAccessWithMutexes(
  val globalVar: XcfaGlobalVar,
  label: XcfaLabel,
  access: AccessType,
  acquiredMutexes: Set<String>,
  blockingMutexes: Set<String>,
) : GlobalAccessWithMutexes(label, access, acquiredMutexes, blockingMutexes)

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
  access: AccessType,
  acquiredMutexes: Set<String>,
  blockingMutexes: Set<String>,
) : GlobalAccessWithMutexes(label, access, acquiredMutexes, blockingMutexes)

/**
 * Returns the global variable accesses of the label.
 *
 * @param xcfa the XCFA that contains the label
 * @param currentMutexes the set of mutexes currently acquired by the process of the label
 * @return the list of global variable accesses (c.f., [GlobalVarAccessWithMutexes])
 */
private fun XcfaLabel.getGlobalVarsWithNeededMutexes(
  xcfa: XCFA,
  currentMutexes: Set<String>,
): List<GlobalVarAccessWithMutexes> {
  val globalVars = xcfa.globalVars
  val acquiredMutexes = currentMutexes.toMutableSet()
  val blockingMutexes = mutableSetOf<String>()
  val accesses = mutableListOf<GlobalVarAccessWithMutexes>()
  getFlatLabels().forEach { label ->
    if (label is FenceLabel) {
      acquiredMutexes.addAll(label.acquiredMutexes.map { it.name })
      blockingMutexes.addAll(label.blockingMutexes.map { it.name })
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
            )
          )
        }
      }
    }
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
  currentMutexes: Set<String>,
  xcfa: XCFA,
  parseContext: ParseContext,
): List<MemoryAccessWithMutexes> {
  val acquiredMutexes = currentMutexes.toMutableSet()
  val blockingMutexes = mutableSetOf<String>()
  val accesses = mutableListOf<MemoryAccessWithMutexes>()
  val changedVars = mutableSetOf<VarDecl<*>>()
  getFlatLabels().forEach { label ->
    if (label is FenceLabel) {
      acquiredMutexes.addAll(label.acquiredMutexes.map { it.name })
      blockingMutexes.addAll(label.blockingMutexes.map { it.name })
    } else {
      label.dereferencesWithAccessType.forEach { (deref, access) ->
        val vars = ExprUtils.getVars(deref.array) + ExprUtils.getVars(deref.offset)
        check(changedVars.intersect(vars).isEmpty()) {
          "Cannot handle dereferences with changed variables in between: $this"
        }
        if (
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
              deref.addressesAtomicData(xcfa, parseContext),
              access,
              acquiredMutexes.toSet(),
              blockingMutexes.toSet(),
            )
          )
        }
      }
    }
    label.collectVarsWithAccessType().forEach { (v, access) ->
      if (access.isWritten) changedVars.add(v)
    }
  }
  return accesses
}

/**
 * Checks whether the two given memory locations may be the same under the given state.
 *
 * @param array1 the array expression of the first memory location
 * @param offset1 the offset expression of the first memory location
 * @param array2 the array expression of the second memory location
 * @param offset2 the offset expression of the second memory location
 * @param state the state to check under
 * @return true if the two memory locations may be the same, false otherwise
 */
private fun mayBeSameMemoryLocation(
  array1: Expr<*>,
  offset1: Expr<*>,
  array2: Expr<*>,
  offset2: Expr<*>,
  state: XcfaState<out PtrState<out ExprState>>,
): Boolean {
  var expr: Expr<BoolType> = And(Eq(array1, array2), Eq(offset1, offset2))
  expr =
    (state.sGlobal.innerState as? ExplState)?.let { s -> ExprUtils.simplify(expr, s.`val`) }
      ?: ExprUtils.simplify(expr)
  val possibleSameLocation =
    try {
      WithPushPop(dependencySolver).use {
        dependencySolver.add(PathUtils.unfold(state.sGlobal.toExpr(), 0))
        dependencySolver.add(PathUtils.unfold(expr, 0))
        dependencySolver.check().isSat
      }
    } catch (_: Exception) {
      // TODO this is reached when having incomplete dereferences, we should do it properly
      true
    }
  if (!possibleSameLocation) return false

  val pointerPartitions = state.xcfa!!.getPointerPartitions()
  val a1 = (array1 as? RefExpr<*>)?.decl ?: return true // cannot decide
  val a2 = (array2 as? RefExpr<*>)?.decl ?: return true // cannot decide
  return pointerPartitions.any { a1 in it.first && a2 in it.first }
}

private fun canExecuteConcurrently(
  access1: GlobalAccessWithMutexes,
  access2: GlobalAccessWithMutexes,
): Boolean =
  (access1.acquiredMutexes intersect access2.blockingMutexes).isEmpty() &&
    (access2.acquiredMutexes intersect access1.blockingMutexes).isEmpty()
