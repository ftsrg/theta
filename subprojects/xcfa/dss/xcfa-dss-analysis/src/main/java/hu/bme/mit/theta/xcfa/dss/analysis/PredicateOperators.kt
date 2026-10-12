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
package hu.bme.mit.theta.xcfa.dss.analysis

import hu.bme.mit.theta.analysis.pred.PredPrec
import hu.bme.mit.theta.analysis.ptr.PtrPrec
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolExprs.False
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Not
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.PathUtils
import hu.bme.mit.theta.solver.Solver
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.xcfa.analysis.XcfaPrec

/**
 * The solver-backed operators of CPAchecker's distributed predicate CPA, over plain Theta
 * expressions:
 * - [isUnsat]: `ProceedPredicateStateOperator.processBackward` (an unsatisfiable violation
 *   condition is dropped) and the `hasRootAsPredecessor` check of
 *   `PredicateViolationConditionOperator`;
 * - [isSubsumed]: `PredicateStateCoverageOperator.isSubsumed` (state 1 implies state 2).
 *
 * The solver is created lazily, on the thread of the first query, under the same lock that guards
 * checker construction (see [runWorkerConfig]): constructing native solver contexts concurrently is
 * what has crashed Z3 before. A block worker is confined to one thread, so after creation the
 * solver is only ever touched by that thread.
 */
class DssPredicateOperators(private val solverFactory: SolverFactory) {

  private val solver: Solver by lazy { withSolverConstructionLock { solverFactory.createSolver() } }

  fun isUnsat(expr: Expr<BoolType>): Boolean {
    if (expr == False()) return true
    if (expr == True()) return false
    solver.push()
    try {
      solver.add(PathUtils.unfold(expr, 0))
      return solver.check().isUnsat
    } finally {
      solver.pop()
    }
  }

  fun isSubsumed(state1: Expr<BoolType>, state2: Expr<BoolType>): Boolean =
    state2 == True() || state1 == state2 || isUnsat(And(state1, Not(state2)))
}

/**
 * The predicates a block transmits as its precision, extracted from the expressions of a safe
 * result (CPAchecker transmits the `PredicatePrecision` of the analysis alongside every state;
 * Theta's checkers do not return their final precision, but every reached predicate state is a
 * boolean combination of the predicates of that precision, so the atoms of the reached states are
 * the part of the precision that actually mattered). Auxiliary violation-condition variables
 * ([DssAuxVars]) are filtered out, they are meaningless outside of the condition they belong to.
 */
fun predicatesOf(exprs: Iterable<Expr<BoolType>>): Set<Expr<BoolType>> =
  exprs
    .flatMap(ExprUtils::getAtoms)
    .filter { it != True() && it != False() }
    .filter { atom -> ExprUtils.getVars(atom).none(DssAuxVars::isAux) }
    .toSet()

/**
 * CPAchecker's `CombinePredicatePrecisionOperator`: the union of [precisions], restricted to
 * predicates over variables that occur in every one of them - if at least one variable does, and
 * otherwise to predicates over any variable of any of them (i.e., the plain union).
 */
fun combinePredicatePrecisions(precisions: Collection<Set<Expr<BoolType>>>): Set<Expr<BoolType>> {
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

/**
 * The predicates of a predicate-abstraction precision ([predicatePrecision]'s shape), filtered like
 * [predicatesOf]; empty for any other precision.
 */
fun predicatesOfPrecision(precision: XcfaPrec<*>): Set<Expr<BoolType>> =
  ((precision.p as? PtrPrec<*>)?.innerPrec as? PredPrec)?.preds?.let(::predicatesOf) ?: emptySet()

/** The initial precision a predicate-abstraction checker is started with for [predicates]. */
fun predicatePrecision(predicates: Set<Expr<BoolType>>): XcfaPrec<PtrPrec<PredPrec>> =
  XcfaPrec(PtrPrec(PredPrec.of(predicates), emptySet()))
