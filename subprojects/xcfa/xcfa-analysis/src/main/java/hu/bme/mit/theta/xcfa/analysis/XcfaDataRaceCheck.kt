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
import hu.bme.mit.theta.core.type.anytype.RefExpr
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
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.passes.changeVars
import hu.bme.mit.theta.xcfa.utils.*

private val dependencySolver: Solver by lazy { Z3SolverFactory.getInstance().createSolver() }

/**
 * Whether this pointer addresses an `_Atomic` object -- accesses to which are, by definition, not
 * data races with anything.
 *
 * A race between two *variables* checks whether the **variable** is atomic (`!v1.globalVar.atomic`,
 * below). An access *through* a pointer touches what the pointer points **at**, which is a
 * different question, and `_Atomic` says which is which:
 * ```
 * _Atomic int *p;   // p is an ordinary variable; p[i] is atomic, and cannot be raced on
 * int * _Atomic p;  // p itself is atomic; what it points at is not
 * ```
 *
 * A pointer variable can simply be asked. An **address-taken** object cannot: `&x` is folded to a
 * bare literal -- the object's id -- long before the analysis runs, and the C types are keyed by
 * object *identity*, so an expression any pass rebuilds has lost its type anyway. What survives is
 * the pointer [ReferenceElimination] invents for such a variable: it holds that same id, and it was
 * told what it points at. So the id is looked up there.
 *
 * Nothing found means nothing skipped -- reporting a race is the safe direction.
 */
private fun Expr<*>.addressesAtomicData(xcfa: XCFA, parseContext: ParseContext): Boolean {
  // A pointer *variable*: its type says what it points at.
  (this as? RefExpr<*>)?.decl?.let { decl ->
    xcfa.globalVars
      .firstOrNull { it.wrappedVar == decl }
      ?.let { if (it.pointsToAtomic) return true }
    val pointee =
      try {
        when (val type = CComplexType.getType(this, parseContext)) {
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
  return xcfa.globalVars.any { it.pointsToAtomic && it.initValue == this }
}

/** Returns a predicate that checks whether data race is possible after the given state. */
fun getDataRaceDetector(parseContext: ParseContext) =
  object : XcfaErrorDetector {

    override fun test(s: XcfaState<out PtrState<out ExprState>>): Boolean =
      getDataRaceCondition(s) != null

    private fun getDataRaceCondition(s: XcfaState<out PtrState<out ExprState>>): Expr<BoolType>? {
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
                    return True()
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
                    return And(Eq(m1.array, m2.array), Eq(m1.offset, m2.offset))
                  }
                }
              }
            }
          }
        }
      }
      return null
    }

    override fun exprTraceCheckerWrapper(
      exprTraceChecker: ExprTraceChecker<Refutation>
    ): ExprTraceChecker<Refutation> = ExprTraceChecker { trace ->
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
          getDataRaceCondition(lastState)?.let { extraAssumption ->
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
  }

private sealed class GlobalAccessWithMutexes(
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
  access: AccessType,
  acquiredMutexes: Set<String>,
  blockingMutexes: Set<String>,
) : GlobalAccessWithMutexes(access, acquiredMutexes, blockingMutexes)

/**
 * Represents a memory access: stores the array expression, the offset expression, the access type
 * (read/write) and the set of acquired/blocking mutexes for performing the variable access.
 */
private class MemoryAccessWithMutexes(
  val array: Expr<*>,
  val offset: Expr<*>,
  /** The cell is `_Atomic`, so nothing that touches it races with anything. */
  val atomic: Boolean,
  access: AccessType,
  acquiredMutexes: Set<String>,
  blockingMutexes: Set<String>,
) : GlobalAccessWithMutexes(access, acquiredMutexes, blockingMutexes)

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
            GlobalVarAccessWithMutexes(v, access, acquiredMutexes.toSet(), blockingMutexes.toSet())
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
              deref.array,
              deref.offset,
              deref.array.addressesAtomicData(xcfa, parseContext),
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
