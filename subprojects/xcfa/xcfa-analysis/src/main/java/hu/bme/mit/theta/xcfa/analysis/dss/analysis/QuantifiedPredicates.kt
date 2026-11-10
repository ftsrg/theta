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
package hu.bme.mit.theta.xcfa.analysis.dss.analysis

import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.AndExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.False
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.ExistsExpr
import hu.bme.mit.theta.core.type.booltype.ForallExpr
import hu.bme.mit.theta.core.type.booltype.ImplyExpr
import hu.bme.mit.theta.core.type.booltype.NotExpr
import hu.bme.mit.theta.core.type.booltype.OrExpr
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Not
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Or
import hu.bme.mit.theta.core.utils.PathUtils
import hu.bme.mit.theta.solver.Solver
import hu.bme.mit.theta.solver.SolverManager

/**
 * What DSS does with the quantified formulas a block checker's proof can bring in: `Z3:new`
 * interpolates by a Horn query, whose answer may keep quantifiers that other solvers cannot take.
 */
enum class DssQuantifiedPredicates {
  /** They stay; a DSS query that the solver fails on is undecided, so the verdict is unknown. */
  KEEP,
  /** They stay, and a DSS query that fails on the main solver is retried on the fallback one. */
  FALLBACK,
  /** Before they leave the block, their quantified parts are weakened away. */
  DROP,
  /** Their quantifiers are eliminated by Z3; what elimination leaves is weakened away. */
  ELIMINATE,
}

/** The solver of [DssQuantifierCleaner]: only `Z3:new` implements quantifier elimination. */
const val QUANTIFIER_ELIMINATION_SOLVER = "Z3:new"

private val QUANTIFIER_ELIMINATION_TACTICS = listOf("qe", "qe2")

fun hasQuantifier(expr: Expr<*>): Boolean =
  expr is ExistsExpr || expr is ForallExpr || expr.ops.any(::hasQuantifier)

/**
 * A quantifier-free formula implied by [expr]: a quantified subformula becomes true where it occurs
 * positively and false where it occurs negatively. A subformula under both polarities (an iff, an
 * ite) that contains one is replaced as a whole the same way.
 */
fun withoutQuantifiers(expr: Expr<BoolType>): Expr<BoolType> = weaken(expr, positive = true)

private fun weaken(expr: Expr<BoolType>, positive: Boolean): Expr<BoolType> =
  when {
    !hasQuantifier(expr) -> expr
    expr is NotExpr -> Not(weaken(expr.op, !positive))
    expr is AndExpr -> And(expr.ops.map { weaken(it, positive) })
    expr is OrExpr -> Or(expr.ops.map { weaken(it, positive) })
    expr is ImplyExpr -> Or(Not(weaken(expr.leftOp, !positive)), weaken(expr.rightOp, positive))
    positive -> True()
    else -> False()
  }

/** [expr] with every outermost quantified subformula replaced by [eliminate]'s equivalent. */
fun replaceQuantified(
  expr: Expr<BoolType>,
  eliminate: (Expr<BoolType>) -> Expr<BoolType>,
): Expr<BoolType> =
  when {
    !hasQuantifier(expr) -> expr
    expr is ExistsExpr || expr is ForallExpr -> eliminate(expr)
    else ->
      expr.withOps(
        expr.ops.map {
          @Suppress("UNCHECKED_CAST")
          if (it.type is BoolType) replaceQuantified(it as Expr<BoolType>, eliminate) else it
        }
      )
  }

/**
 * Makes the formulas leaving a block quantifier-free as [mode] says; `KEEP` and `FALLBACK` leave
 * them. [clean] only weakens, which keeps a postcondition an over-approximation and only changes
 * which predicates a precision has. A witness state takes [equivalent]: a backward witness
 * complements it, and the complement of a weaker state is stronger.
 */
class DssQuantifierCleaner(private val mode: DssQuantifiedPredicates) {

  private val solver: Solver by lazy {
    withSolverConstructionLock {
      SolverManager.resolveSolverFactory(QUANTIFIER_ELIMINATION_SOLVER).createSolver()
    }
  }

  private val eliminated = HashMap<Expr<BoolType>, Expr<BoolType>>()

  fun clean(expr: Expr<BoolType>): Expr<BoolType> =
    when {
      !hasQuantifier(expr) -> expr
      mode == DssQuantifiedPredicates.DROP -> withoutQuantifiers(expr)
      mode == DssQuantifiedPredicates.ELIMINATE ->
        withoutQuantifiers(replaceQuantified(expr) { eliminated.getOrPut(it) { eliminate(it) } })
      else -> expr
    }

  /** [expr] with what ELIMINATE removes exactly; the quantifiers it cannot remove stay. */
  fun equivalent(expr: Expr<BoolType>): Expr<BoolType> =
    if (mode != DssQuantifiedPredicates.ELIMINATE || !hasQuantifier(expr)) expr
    else replaceQuantified(expr) { eliminated.getOrPut(it) { eliminate(it) } }

  /**
   * A failing tactic hands its input back, so the next one gets to try. The solver speaks of
   * constants, so the variables are unfolded first, as for a query.
   */
  private fun eliminate(quantified: Expr<BoolType>): Expr<BoolType> =
    PathUtils.foldin(
      QUANTIFIER_ELIMINATION_TACTICS.fold(PathUtils.unfold(quantified, 0)) { current, tactic ->
        if (hasQuantifier(current)) solver.eliminateQuantifiers(current, tactic) else current
      },
      0,
    )
}
