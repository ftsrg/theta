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
package hu.bme.mit.theta.analysis.algorithm.mdd

import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr
import hu.bme.mit.theta.analysis.algorithm.mdd.cegar.MddCegarChecker
import hu.bme.mit.theta.analysis.expr.refinement.createSeqItpCheckerFactory
import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Add
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Geq
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Leq
import hu.bme.mit.theta.core.type.anytype.Exprs.Prime
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Not
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.solver.SolverPool
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

/**
 * With the witness-caching lower bound held fixed, both upper bounds reduce solver checks, but the
 * SAT-cache bound prunes more than the reach-set constraint.
 *
 * The reach constraint is a target-only postcondition: it permits any transition whose target is
 * reachable. The bound is a relation: it permits a transition only if its source was reached and the
 * source→target step is SAT — and since a SAT step from a reached source lands in the reach set,
 * `bound ⊆ reach`. So the bound additionally prunes steps that are infeasible from their (reached)
 * source yet land in a reachable target, which the target-only postcondition cannot express. The
 * coupling `y' ∈ [y, y+x]` creates exactly such steps (from high `y` a lower `y` is unreachable since
 * `y' ≥ y`, yet that lower `y` is reachable from a smaller-`y` state). Both agree on the verdict (the
 * bound is a sound replacement for the reach constraint), but the bound issues strictly fewer checks.
 */
class MddBoundVsReachTest {

  private data class Run(val safe: Boolean, val checks: Long)

  @Test
  fun boundIsCheaperThanReachConstraintUnderCaching() {
    val x = Decls.Var("x", IntType.getInstance())
    val y = Decls.Var("y", IntType.getInstance())
    val init = And(Eq(x.ref, Int(0)), Eq(y.ref, Int(0)))
    val tran =
      And(
        Eq(Prime(x.ref), Add(x.ref, Int(1))),
        Leq(Prime(x.ref), Int(8)),
        Geq(Prime(y.ref), y.ref),
        Leq(Prime(y.ref), Add(y.ref, x.ref)),
      )
    val prop = Not(Eq(x.ref, Int(5)))

    // same caching lower bound; reach upper bound vs SAT-cache upper bound
    val reach = run(init, tran, prop, useReachConstraint = true, useTransitionBound = false)
    val bound = run(init, tran, prop, useReachConstraint = false, useTransitionBound = true)

    assertEquals(reach.safe, bound.safe)
    assertTrue(bound.checks < reach.checks, "bound=${bound.checks}, reach=${reach.checks}")
  }

  private fun run(
    init: Expr<BoolType>,
    tran: Expr<BoolType>,
    prop: Expr<BoolType>,
    useReachConstraint: Boolean,
    useTransitionBound: Boolean,
  ): Run {
    SolverPool(Z3LegacySolverFactory.getInstance()).use { solverPool ->
      val checker =
        MddCegarChecker(
          MonolithicExpr(init, tran, prop),
          solverPool,
          NullLogger.getInstance(),
          createSeqItpCheckerFactory(Z3LegacySolverFactory.getInstance()),
          useReachConstraint = useReachConstraint,
          useTransitionSeeding = true,
          useTransitionBound = useTransitionBound,
        )
      return Run(checker.check(null).isSafe, solverPool.checkCount)
    }
  }
}
