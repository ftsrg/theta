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
import hu.bme.mit.theta.analysis.expr.refinement.createSeqItpCheckerFactory
import hu.bme.mit.theta.common.logging.ConsoleLogger
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.common.stopwatch.Stopwatch
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
import hu.bme.mit.theta.core.type.inttype.IntExprs.Lt
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.solver.SolverPool
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.MethodSource

/**
 * Runs [MddCegarChecker] on the same model with identical configuration except for
 * [MddCegarChecker.useReachConstraint] and [MddCegarChecker.useTransitionSeeding], to compare the
 * effect of constraining each iteration's saturation to the previous iteration's reach set and of
 * seeding each iteration's relation from the previous iteration's concrete witnesses. On-the-fly reachability is disabled in both
 * runs because it cannot be used in constrained iterations. The models are the multi-iteration
 * rows of [MddCegarCheckerTest]; single-iteration models never build a constraint, so a
 * comparison on them would be vacuous.
 */
class MddCegarConstraintComparisonTest {

  private data class RunResult(val safe: Boolean, val solverChecks: Long, val timeMs: Long)

  companion object {
    private val X = Decls.Var("x", IntType.getInstance())
    private val Y = Decls.Var("y", IntType.getInstance())
    private val Z = Decls.Var("z", IntType.getInstance())

    @JvmStatic
    fun data(): Collection<Arguments> =
      listOf(
        Arguments.of(
          // x = 0, x' = x + 1 & x' <= 10, not x = 5
          Eq(X.ref, Int(0)),
          And(Eq(Prime(X.ref), Add(X.ref, Int(1))), Leq(Prime(X.ref), Int(10))),
          Not(Eq(X.ref, Int(5))),
          false,
        ),
        Arguments.of(
          Eq(X.ref, Int(0)),
          And(Eq(Prime(X.ref), Add(X.ref, Int(1))), Leq(Prime(X.ref), Int(5))),
          Not(Eq(X.ref, Int(5))),
          false,
        ),
        // deep counterexample: interpolation climbs one predicate per iteration, so the relation
        // is rebuilt many times and seeding can carry it over
        Arguments.of(
          Eq(X.ref, Int(0)),
          And(Eq(Prime(X.ref), Add(X.ref, Int(1))), Leq(Prime(X.ref), Int(10))),
          Not(Eq(X.ref, Int(10))),
          false,
        ),
        // noise variable y coupled to x (y' in [y, y+x]): the concrete state space and relation
        // grow triangularly and cannot share sub-MDDs across x values, while the property never
        // mentions y, so the abstraction drops it entirely
        Arguments.of(
          And(Eq(X.ref, Int(0)), Eq(Y.ref, Int(0))),
          And(
            Eq(Prime(X.ref), Add(X.ref, Int(1))),
            Leq(Prime(X.ref), Int(8)),
            Geq(Prime(Y.ref), Y.ref),
            Leq(Prime(Y.ref), Add(Y.ref, X.ref)),
          ),
          Not(Eq(X.ref, Int(9))),
          true,
        ),
        Arguments.of(
          And(Eq(X.ref, Int(0)), Eq(Y.ref, Int(0))),
          And(
            Eq(Prime(X.ref), Add(X.ref, Int(1))),
            Leq(Prime(X.ref), Int(8)),
            Geq(Prime(Y.ref), Y.ref),
            Leq(Prime(Y.ref), Add(Y.ref, X.ref)),
          ),
          Not(Eq(X.ref, Int(5))),
          false,
        ),
        // safe ladder: x stays even, but proving x=9 unreachable needs one new predicate per
        // iteration (x!=7, x!=5, ...)
        Arguments.of(
          Eq(X.ref, Int(0)),
          And(Eq(Prime(X.ref), Add(X.ref, Int(2))), Leq(Prime(X.ref), Int(12))),
          Not(Eq(X.ref, Int(9))),
          true,
        ),
        Arguments.of(
          Eq(X.ref, Int(0)),
          And(Eq(Prime(X.ref), Add(X.ref, Int(1))), Leq(Prime(X.ref), Int(4))),
          Not(Eq(X.ref, Int(5))),
          true,
        ),
        Arguments.of(
          And(Eq(X.ref, Int(0)), Eq(Y.ref, Int(0)), Eq(Z.ref, Int(0))),
          And(
            And(
              Eq(Prime(X.ref), Add(Y.ref, Int(1))),
              Eq(Prime(Y.ref), Add(Z.ref, Int(1))),
              Eq(Prime(Z.ref), Add(Z.ref, Int(1))),
            ),
            Lt(Prime(Z.ref), Int(10)),
          ),
          Not(Eq(X.ref, Int(5))),
          false,
        ),
        Arguments.of(
          And(Eq(X.ref, Int(0)), Eq(Y.ref, Int(0)), Eq(Z.ref, Int(0))),
          And(
            And(
              Eq(Prime(X.ref), Add(Y.ref, Int(1))),
              Eq(Prime(Y.ref), Add(Z.ref, Int(1))),
              Eq(Prime(Z.ref), Add(Z.ref, Int(1))),
            ),
            Lt(Prime(Z.ref), Int(6)),
          ),
          Not(Eq(X.ref, Int(5))),
          false,
        ),
        Arguments.of(
          And(Eq(X.ref, Int(0)), Eq(Y.ref, Int(0)), Eq(Z.ref, Int(0))),
          And(
            And(
              Eq(Prime(X.ref), Add(Y.ref, Int(1))),
              Eq(Prime(Y.ref), Add(Z.ref, Int(1))),
              Eq(Prime(Z.ref), Add(Z.ref, Int(1))),
            ),
            Lt(Prime(Z.ref), Int(5)),
          ),
          Not(Eq(X.ref, Int(5))),
          true,
        ),
      )
  }

  @MethodSource("data")
  @ParameterizedTest(name = "{index}: {0}, {1}, {2}, {3}")
  fun compare(
    initExpr: Expr<BoolType>,
    tranExpr: Expr<BoolType>,
    propExpr: Expr<BoolType>,
    safe: Boolean,
  ) {
    val constrained = run(initExpr, tranExpr, propExpr, useReachConstraint = true)
    val unconstrained = run(initExpr, tranExpr, propExpr, useReachConstraint = false)
    val seeded =
      run(initExpr, tranExpr, propExpr, useReachConstraint = true, useTransitionSeeding = true)
    val nonCegar = runNonCegar(initExpr, tranExpr, propExpr)

    println(
      "Reach-constraint comparison for $tranExpr ($propExpr): " +
        "constrained: solverChecks=${constrained.solverChecks}, time=${constrained.timeMs}ms; " +
        "unconstrained: solverChecks=${unconstrained.solverChecks}, time=${unconstrained.timeMs}ms; " +
        "constrained+seeded: solverChecks=${seeded.solverChecks}, time=${seeded.timeMs}ms; " +
        "nonCegar: solverChecks=${nonCegar.solverChecks}, time=${nonCegar.timeMs}ms"
    )

    assertEquals(safe, constrained.safe)
    assertEquals(safe, unconstrained.safe)
    assertEquals(safe, seeded.safe)
    assertEquals(safe, nonCegar.safe)
  }

  private fun runNonCegar(
    initExpr: Expr<BoolType>,
    tranExpr: Expr<BoolType>,
    propExpr: Expr<BoolType>,
  ): RunResult {
    SolverPool(Z3LegacySolverFactory.getInstance()).use { solverPool ->
      val checker =
        MddChecker(
          MonolithicExpr(initExpr, tranExpr, propExpr),
          solverPool,
          ConsoleLogger(Logger.Level.MAINSTEP),
        )
      val stopwatch = Stopwatch.createStarted()
      val status = checker.check(null)
      stopwatch.stop()
      return RunResult(status.isSafe, solverPool.checkCount, stopwatch.elapsedMillis())
    }
  }

  private fun run(
    initExpr: Expr<BoolType>,
    tranExpr: Expr<BoolType>,
    propExpr: Expr<BoolType>,
    useReachConstraint: Boolean,
    useTransitionSeeding: Boolean = false,
  ): RunResult {
    SolverPool(Z3LegacySolverFactory.getInstance()).use { solverPool ->
      val logger = ConsoleLogger(Logger.Level.MAINSTEP)
      val checker =
        MddCegarChecker(
          MonolithicExpr(initExpr, tranExpr, propExpr),
          solverPool,
          logger,
          createSeqItpCheckerFactory(Z3LegacySolverFactory.getInstance()),
          useReachConstraint = useReachConstraint,
          useOnTheFlyReachability = false,
          useTransitionSeeding = useTransitionSeeding,
        )
      val stopwatch = Stopwatch.createStarted()
      val status = checker.check(null)
      stopwatch.stop()
      return RunResult(status.isSafe, solverPool.checkCount, stopwatch.elapsedMillis())
    }
  }
}
