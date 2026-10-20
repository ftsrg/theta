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
package hu.bme.mit.theta.xcfa.analysis.dss

import hu.bme.mit.theta.analysis.pred.PredPrec
import hu.bme.mit.theta.analysis.ptr.PtrPrec
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.False
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Not
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.PathUtils
import hu.bme.mit.theta.solver.Solver
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.solver.utils.WithPushPop
import hu.bme.mit.theta.xcfa.analysis.XcfaPrec

/**
 * Solver-backed operators of CPAchecker's distributed predicate CPA. A query the solver fails on
 * throws [DssUndecidedQueryException]: it must never be taken as satisfiable or unsatisfiable.
 */
class DssPredicateOperators(solverFactory: SolverFactory) {

  private val solver = OperatorSolver(solverFactory)

  fun isUnsat(expr: Expr<BoolType>): Boolean {
    if (expr == False()) return true
    if (expr == True()) return false
    return try {
      solver.isUnsat(expr)
    } catch (e: Exception) {
      throw DssUndecidedQueryException(e)
    }
  }

  fun isLeq(state1: Expr<BoolType>, state2: Expr<BoolType>): Boolean =
    state2 == True() || state1 == state2 || isUnsat(And(state1, Not(state2)))
}

/** A query of [DssPredicateOperators] the solver failed on; DSS reports an unknown verdict. */
class DssUndecidedQueryException(cause: Throwable) :
  RuntimeException("DSS solver query undecided: $cause", cause)

/** A solver that threw is replaced by a fresh one. */
private class OperatorSolver(private val factory: SolverFactory) {

  private var solver: Solver? = null

  fun isUnsat(expr: Expr<BoolType>): Boolean {
    val current =
      solver ?: withSolverConstructionLock { factory.createSolver() }.also { solver = it }
    try {
      WithPushPop(current).use {
        current.add(PathUtils.unfold(expr, 0))
        return current.check().isUnsat
      }
    } catch (e: Exception) {
      solver = null
      runCatching { current.close() }
      throw e
    }
  }
}

/** A block's transmitted precision: the atoms of its reached states, without [DssAuxVars]. */
fun Iterable<Expr<BoolType>>.collectPreds(): Set<Expr<BoolType>> =
  flatMap(ExprUtils::getAtoms)
    .filter { it != True() && it != False() }
    .filter { atom -> ExprUtils.getVars(atom).none(DssAuxVars::isAux) }
    .toSet()

/** CPAchecker's `CombinePredicatePrecisionOperator`. */
fun combinePredPrecs(precisions: Collection<Set<Expr<BoolType>>>): Set<Expr<BoolType>> {
  if (precisions.isEmpty()) return emptySet()
  if (precisions.size == 1) return precisions.single()
  val count = HashMap<Any, Int>()
  for (precision in precisions) {
    for (variable in ExprUtils.getVars(precision)) count.merge(variable, 1, Int::plus)
  }
  val inAll = count.filterValues { it == precisions.size }.keys
  val important = inAll.ifEmpty { count.keys }
  return precisions
    .flatten()
    .filter { predicate -> ExprUtils.getVars(predicate).any { it in important } }
    .toSet()
}

fun XcfaPrec<*>.collectPreds(): Set<Expr<BoolType>> =
  ((p as? PtrPrec<*>)?.innerPrec as? PredPrec)?.preds?.collectPreds() ?: emptySet()

fun getPredPrec(predicates: Set<Expr<BoolType>>): XcfaPrec<PtrPrec<PredPrec>> =
  XcfaPrec(PtrPrec(PredPrec.of(predicates), emptySet()))
