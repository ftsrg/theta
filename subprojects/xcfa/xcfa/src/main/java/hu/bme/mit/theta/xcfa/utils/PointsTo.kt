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
package hu.bme.mit.theta.xcfa.utils

import com.google.common.base.Preconditions.checkState
import hu.bme.mit.theta.common.Try
import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.ImmutableValuation
import hu.bme.mit.theta.core.model.MutableValuation
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.Stmts.Assign
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.NullaryExpr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.ModExpr
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.StmtSimplifier
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.xcfa.model.*

data class MallocLitExpr<T : Type>(val kType: T) : NullaryExpr<T>(), LitExpr<T> {

  override fun getType(): T = kType

  override fun eval(valuation: Valuation): LitExpr<T> = this
}

/**
 * Calculates the points-to graph of the XCFA, i.e., for each pointer variable, the set of possible
 * literals it may point to. If `initEdges` is given, only possible values after the init phase are
 * included (e.g., null initializer is excluded in most cases).
 */
fun XCFA.getPointsToGraph(initEdges: Set<XcfaEdge> = setOf()): Map<VarDecl<*>, Set<LitExpr<*>>> {
  val attempt =
    Try.attempt {
      fun unboxMod(e: Expr<*>): Expr<*> = if (e is ModExpr<*>) unboxMod(e.ops[0]) else e

      val bases =
        this.procedures
          .flatMap { proc ->
            (proc.edges - initEdges).flatMap { edge ->
              edge.getFlatLabels().flatMap { label ->
                label.dereferences.map { unboxMod(it.array) }
              }
            }
          }
          .filter { it !is LitExpr<*> && it !is Dereference<*, *, *> }
          .toSet()
      checkState(bases.all { it is RefExpr<*> })

      // value assignments are either assignments, or thread start statements, or procedure invoke
      // statements, or coming from the valuation after the init phase (if initEdges is given)
      val assignments =
        this.procedures.flatMap { proc ->
          (proc.edges - initEdges).flatMap { edge ->
            edge
              .getFlatLabels()
              .filter { it is StmtLabel && it.stmt is AssignStmt<*> }
              .map { (it as StmtLabel).stmt as AssignStmt<*> }
          }
        }
      val threadStart =
        this.procedures.flatMap { proc ->
          proc.edges // initEdges cannot contain thread starts
            .flatMap { it.getFlatLabels().filterIsInstance<StartLabel>() }
            .flatMap {
              val calledProc = this.procedures.find { proc -> proc.name == it.name }
              calledProc?.let { proc ->
                proc.params
                  .withIndex()
                  .filter { (_, it) -> it.second != ParamDirection.OUT }
                  .map { (i, pair) ->
                    val (param, _) = pair
                    Assign(cast(param, param.type), cast(it.params[i], param.type))
                  } +
                  proc.params
                    .withIndex()
                    .filter { (i, pair) ->
                      pair.second != ParamDirection.IN && it.params[i] is RefExpr<*>
                    }
                    .map { (i, pair) ->
                      val (param, _) = pair
                      Assign(
                        cast((it.params[i] as RefExpr<*>).decl as VarDecl<*>, param.type),
                        cast(param.ref, param.type),
                      )
                    }
              } ?: listOf()
            }
        }
      val procInvoke =
        this.procedures.flatMap { proc ->
          proc.edges
            .flatMap { it.getFlatLabels().filterIsInstance<InvokeLabel>() }
            .flatMap {
              val calledProc = this.procedures.find { proc -> proc.name == it.name }
              calledProc?.let { calledProc ->
                calledProc.params
                  .filter { it.second != ParamDirection.OUT }
                  .mapIndexed { i, (param, _) ->
                    Assign(cast(param, param.type), cast(it.params[i], param.type))
                  } +
                  calledProc.params
                    .filter { it.second != ParamDirection.IN }
                    .mapIndexed { i, (param, _) ->
                      Assign(
                        cast((it.params[i] as RefExpr<*>).decl as VarDecl<*>, param.type),
                        cast(param.ref, param.type),
                      )
                    }
              } ?: listOf()
            }
        }
      val initValuation =
        if (initEdges.isNotEmpty()) {
          val valuation = getValuationAfterInitPhase(initProcedureBuilders.first().first, initEdges)
          valuation.toMap().mapNotNull { (k, v) ->
            if (k !is VarDecl<*>) return@mapNotNull null
            Assign(cast(k, k.type), cast(v, k.type))
          }
        } else {
          listOf()
        }

      val allAssignments = (assignments + threadStart + procInvoke + initValuation)

      val ptrVars = LinkedHashSet<VarDecl<*>>(bases.map { (it as RefExpr<*>).decl as VarDecl<*> })
      var lastPtrVars = emptySet<VarDecl<*>>()

      while (ptrVars != lastPtrVars) {
        lastPtrVars = ptrVars.toSet()
        val rhs = allAssignments.filter { ptrVars.contains(it.varDecl) }.map { unboxMod(it.expr) }
        ptrVars.addAll(rhs.filterIsInstance(RefExpr::class.java).map { it.decl as VarDecl<*> })
      }

      val lits = LinkedHashMap<VarDecl<*>, MutableSet<LitExpr<*>>>()
      val alias = LinkedHashMap<VarDecl<*>, MutableSet<VarDecl<*>>>()

      val litAssignments =
        allAssignments
          .filter { ptrVars.contains(it.varDecl) && unboxMod(it.expr) is LitExpr<*> }
          .map { Pair(it.varDecl, unboxMod(it.expr) as LitExpr<*>) } +
          allAssignments
            .filter {
              ptrVars.contains(it.varDecl) &&
                (unboxMod(it.expr) !is LitExpr<*> && unboxMod(it.expr) !is RefExpr<*>)
            }
            .map { Pair(it.varDecl, MallocLitExpr(it.varDecl.type)) }
      litAssignments.forEach { lits.getOrPut(it.first) { LinkedHashSet() }.add(it.second) }
      val varAssignments =
        allAssignments
          .filter { ptrVars.contains(it.varDecl) && unboxMod(it.expr) is RefExpr<*> }
          .map { Pair(it.varDecl, (unboxMod(it.expr) as RefExpr<*>).decl as VarDecl<*>) }
      varAssignments.forEach { alias.getOrPut(it.first) { LinkedHashSet() }.add(it.second) }
      varAssignments.forEach { lits.putIfAbsent(it.first, LinkedHashSet()) }

      var lastLits = emptyMap<VarDecl<*>, MutableSet<LitExpr<*>>>()
      while (lastLits != lits) {
        lastLits = lits.entries.associate { (k, v) -> k to v.toMutableSet() }
        alias.forEach {
          lits
            .getOrPut(it.key) { LinkedHashSet() }
            .addAll(it.value.flatMap { lits.getOrDefault(it, emptySet()) })
        }
      }

      lits.filter { bases.contains(it.key.ref) }
    }
  return if (attempt.isSuccess) {
    attempt.asSuccess().value
  } else {
    emptyMap()
  }
}

fun Collection<VarDecl<*>>.pointsTo(xcfa: XCFA) =
  flatMap { xcfa.pointsToGraph[it] ?: emptyList() }.toSet()

fun VarAccessMap.pointsTo(xcfa: XCFA) = keys.pointsTo(xcfa)

/**
 * Returns the set of possible values of the expression, or null if it cannot be determined (e.g.,
 * if it depends on non-pointer variables). It is calculated by substituting all pointer variables
 * with their points-to sets, and taking their Cartesian product.
 */
fun Expr<*>.pointsTo(xcfa: XCFA): Set<LitExpr<*>>? {
  val results = mutableSetOf<LitExpr<*>>()
  var values = listOf<Map<Decl<*>, LitExpr<*>>>()
  val vars = ExprUtils.getVars(this)
  vars.forEach { v ->
    val pts = xcfa.pointsToGraph[v] ?: return null
    val newValues = mutableListOf<Map<Decl<*>, LitExpr<*>>>()
    pts.forEach { lit ->
      if (values.isEmpty()) {
        newValues.add(mapOf(v to lit))
      } else {
        values.forEach { vs -> newValues.add(vs + mapOf(v to lit)) }
      }
    }
    values = newValues
  }
  values.forEach { vs ->
    val valuation = ImmutableValuation.from(vs)
    val simplified = ExprUtils.simplify(this, valuation)
    if (simplified !is LitExpr<*>) return null
    results.add(simplified)
  }
  return results
}

private fun getValuationAfterInitPhase(
  builder: XcfaProcedureBuilder,
  initEdges: Set<XcfaEdge>,
): Valuation {
  val initLoc = builder.parent.getInitProcedures().first().first.initLoc
  val initLoops = getInitLoops(initLoc, initEdges)
  val toVisit = initLoc.outgoingEdges.toMutableList()
  val visited = mutableSetOf<XcfaEdge>()
  val valuations = LinkedHashMap<XcfaEdge, Valuation>()
  while (toVisit.isNotEmpty()) {
    val edge =
      toVisit.find { candidate -> candidate.source.incomingEdges.all { it in visited } }
        ?: toVisit.first()
    toVisit.remove(edge)
    visited.add(edge)
    val valuation =
      MutableValuation.copyOf(mergeIncomingValuations(edge.source, valuations, initLoops))
    edge.getFlatLabels().filterIsInstance<StmtLabel>().forEach {
      // update valuation
      it.stmt.accept(StmtSimplifier.StmtSimplifierVisitor(), valuation)
    }
    valuations[edge] = valuation
    toVisit.addAll(edge.target.outgoingEdges.filter { it !in visited && it in initEdges })
  }

  val finalInitEdges =
    initEdges.filter { e1 ->
      e1.target.outgoingEdges.isNotEmpty() && initEdges.none { e2 -> e2.source == e1.target }
    }
  return finalInitEdges.map { valuations[it]!! }.reduce { acc, other -> intersect(acc, other) }
}
