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
import hu.bme.mit.theta.common.logging.ConsoleLogger
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.common.stopwatch.Stopwatch
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Add
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Leq
import hu.bme.mit.theta.core.type.anytype.Exprs.Prime
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Not
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.solver.SolverPool
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory
import org.junit.jupiter.api.Test

class ScratchConstraintRuntimeTest {

  private val x = Decls.Var("x", IntType.getInstance())
  private val y = Decls.Var("y", IntType.getInstance())
  private val z = Decls.Var("z", IntType.getInstance())

  @Test
  fun counter30() {
    // x = 0, x' = x + 1 & x' <= 30, prop not x = 30 (unsafe, one refinement per step)
    measure(
      "counter30",
      Eq(x.ref, Int(0)),
      And(Eq(Prime(x.ref), Add(x.ref, Int(1))), Leq(Prime(x.ref), Int(30))),
      Not(Eq(x.ref, Int(30))),
    )
  }

  //  @Test
  //  fun xyzChain30() {
  //    measure(
  //      "xyzChain30",
  //      And(Eq(x.ref, Int(0)), Eq(y.ref, Int(0)), Eq(z.ref, Int(0))),
  //      And(
  //        And(
  //          Eq(Prime(x.ref), Add(y.ref, Int(1))),
  //          Eq(Prime(y.ref), Add(z.ref, Int(1))),
  //          Eq(Prime(z.ref), Add(z.ref, Int(1))),
  //        ),
  //        Lt(Prime(z.ref), Int(30)),
  //      ),
  //      Not(Eq(x.ref, Int(25))),
  //    )
  //  }

  private fun measure(
    name: String,
    init: Expr<BoolType>,
    tran: Expr<BoolType>,
    prop: Expr<BoolType>,
  ) {
    // unconstrained first: JIT warmup biases against the constrained run
    val onTheFly = run(init, tran, prop, useReachConstraint = false, useOnTheFly = true)
    val unconstrained = run(init, tran, prop, useReachConstraint = false, useOnTheFly = false)
    val constrained = run(init, tran, prop, useReachConstraint = true, useOnTheFly = false)
    println(
      "SCRATCH $name: constrained: solverChecks=${constrained.second}, time=${constrained.third}ms; " +
        "unconstrained: solverChecks=${unconstrained.second}, time=${unconstrained.third}ms; " +
        "onTheFly baseline: solverChecks=${onTheFly.second}, time=${onTheFly.third}ms " +
        "(verdicts: ${constrained.first}/${unconstrained.first}/${onTheFly.first})"
    )
  }

  private fun run(
    init: Expr<BoolType>,
    tran: Expr<BoolType>,
    prop: Expr<BoolType>,
    useReachConstraint: Boolean,
    useOnTheFly: Boolean,
  ): Triple<Boolean, Long, Long> {
    SolverPool(Z3LegacySolverFactory.getInstance()).use { solverPool ->
      val logger = ConsoleLogger(Logger.Level.MAINSTEP)
      val checker =
        MddCegarChecker(
          MonolithicExpr(init, tran, prop),
          solverPool,
          logger,
          createSeqItpCheckerFactory(Z3LegacySolverFactory.getInstance()),
          useReachConstraint = useReachConstraint,
          useOnTheFlyReachability = useOnTheFly,
          traceTimeout = 120,
        )
      val stopwatch = Stopwatch.createStarted()
      val status = checker.check(null)
      stopwatch.stop()
      return Triple(status.isSafe, solverPool.checkCount, stopwatch.elapsedMillis())
    }
  }
}
