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
package hu.bme.mit.theta.xcfa.analysis

import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.PathUtils
import hu.bme.mit.theta.solver.Solver
import hu.bme.mit.theta.solver.utils.WithPushPop
import hu.bme.mit.theta.solver.z3.Z3SolverFactory
import hu.bme.mit.theta.xcfa.model.FenceLabel
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.XcfaEdge
import hu.bme.mit.theta.xcfa.model.XcfaGlobalVar
import hu.bme.mit.theta.xcfa.utils.AccessType
import hu.bme.mit.theta.xcfa.utils.WRITE
import hu.bme.mit.theta.xcfa.utils.collectGlobalVars
import hu.bme.mit.theta.xcfa.utils.collectVarsWithAccessType
import hu.bme.mit.theta.xcfa.utils.dereferencesWithAccessType
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import hu.bme.mit.theta.xcfa.utils.isWritten
import java.util.function.Predicate

private val dependencySolver: Solver by lazy { Z3SolverFactory.getInstance().createSolver() }

/** Returns a predicate that checks whether data race is possible after the given state. */
fun getDataRacePredicate() =
  Predicate<XcfaState<out PtrState<out ExprState>>> { s ->
    val xcfa = s.xcfa!!
    val processes = s.processes.entries.toList()
    for (i in processes.indices) {
      val process1 = processes[i]
      for (j in i + 1 until processes.size) {
        val process2 = processes[j]
        check(process1.key != process2.key)
        for (edge1 in process1.value.locs.peek().outgoingEdges) {
          for (edge2 in process2.value.locs.peek().outgoingEdges) {
            val mutexes1 = s.mutexes.filterValues { process1.key in it }.keys
            val mutexes2 = s.mutexes.filterValues { process2.key in it }.keys

            val globals1 = edge1.getGlobalVarsWithNeededMutexes(xcfa, mutexes1)
            val globals2 = edge2.getGlobalVarsWithNeededMutexes(xcfa, mutexes2)
            for (v1 in globals1) {
              for (v2 in globals2) {
                if (
                  v1.globalVar == v2.globalVar &&
                    !v1.globalVar.atomic &&
                    (v1.access.isWritten || v2.access.isWritten) &&
                    canExecuteConcurrently(v1, v2)
                )
                  return@Predicate true
              }
            }

            val mems1 = edge1.getMemoryAccessesWithMutexes(mutexes1)
            val mems2 = edge2.getMemoryAccessesWithMutexes(mutexes2)
            for (m1 in mems1) {
              for (m2 in mems2) {
                if (
                  (m1.access.isWritten || m2.access.isWritten) &&
                    canExecuteConcurrently(m1, m2) &&
                    mayBeSameMemoryLocation(m1.array, m1.offset, m2.array, m2.offset, s)
                )
                  return@Predicate true
                // TODO: refiner needs to check that the memory locations are really the same
              }
            }
          }
        }
      }
    }
    false
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
  access: AccessType,
  acquiredMutexes: Set<String>,
  blockingMutexes: Set<String>,
) : GlobalAccessWithMutexes(access, acquiredMutexes, blockingMutexes)

/**
 * Returns the global variable accesses of the edge.
 *
 * @param xcfa the XCFA that contains the edge
 * @param currentMutexes the set of mutexes currently acquired by the process of the edge
 * @return the list of global variable accesses (c.f., [GlobalVarAccessWithMutexes])
 */
private fun XcfaEdge.getGlobalVarsWithNeededMutexes(
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
 * Returns the memory accesses of the edge.
 *
 * @param currentMutexes the set of mutexes currently acquired by the process of the edge
 * @return the list of memory accesses (c.f., [MemoryAccessWithMutexes])
 */
private fun XcfaEdge.getMemoryAccessesWithMutexes(
  currentMutexes: Set<String>
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
  return WithPushPop(dependencySolver).use {
    dependencySolver.add(PathUtils.unfold(state.sGlobal.toExpr(), 0))
    dependencySolver.add(PathUtils.unfold(expr, 0))
    dependencySolver.check().isSat
  }
}

private fun canExecuteConcurrently(
  access1: GlobalAccessWithMutexes,
  access2: GlobalAccessWithMutexes,
): Boolean =
  (access1.acquiredMutexes intersect access2.blockingMutexes).isEmpty() &&
    (access2.acquiredMutexes intersect access1.blockingMutexes).isEmpty()
