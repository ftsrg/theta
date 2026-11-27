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

import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.Stmts.Assume
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
import hu.bme.mit.theta.xcfa.model.SequenceLabel
import hu.bme.mit.theta.xcfa.model.StmtLabel
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.XcfaLabel
import hu.bme.mit.theta.xcfa.model.XcfaProcedureBuilder
import hu.bme.mit.theta.xcfa.model.optimizeFurther
import hu.bme.mit.theta.xcfa.passes.ProcedurePass
import hu.bme.mit.theta.xcfa.passes.ProcedurePassManager

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
 * positively and false where negatively (one under both polarities is replaced as a whole).
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

/**
 * [xcfa] with the quantified parts of the assumptions leaving its initial locations weakened away
 * ([withoutQuantifiers]), or [xcfa] itself if there are none. These assumptions are a block
 * program's precondition, so the result is a block program for a solver without quantifiers: a
 * weaker precondition keeps the block's SAFE sound, and only the root's UNSAFE is a verdict, which
 * has no precondition. The copy's locations equal the original ones.
 */
fun withQuantifierFreePrecondition(xcfa: XCFA): XCFA {
  val quantified =
    xcfa.procedures.any { procedure ->
      procedure.initLoc.outgoingEdges.any { weakenAssumes(it.label) != it.label }
    }
  if (!quantified) return xcfa
  return xcfa.optimizeFurther(ProcedurePassManager(listOf(WeakenQuantifiedPreconditionPass)))
}

private object WeakenQuantifiedPreconditionPass : ProcedurePass {
  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    for (edge in builder.initLoc.outgoingEdges.toList()) {
      val label = weakenAssumes(edge.label)
      if (label != edge.label) {
        builder.removeEdge(edge)
        builder.addEdge(edge.withLabel(label))
      }
    }
    return builder
  }
}

private fun weakenAssumes(label: XcfaLabel): XcfaLabel =
  when (label) {
    is SequenceLabel -> label.copy(labels = label.labels.map(::weakenAssumes))
    is StmtLabel -> {
      val stmt = label.stmt
      if (stmt is AssumeStmt && hasQuantifier(stmt.cond))
        label.copy(stmt = Assume(withoutQuantifiers(stmt.cond)))
      else label
    }
    else -> label
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
 * Makes the formulas leaving a block quantifier-free as [mode] says. [clean] only weakens; a
 * witness state takes [equivalent], as a backward witness complements it.
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
