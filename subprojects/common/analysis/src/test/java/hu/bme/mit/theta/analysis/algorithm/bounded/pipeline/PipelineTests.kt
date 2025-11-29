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
package hu.bme.mit.theta.analysis.algorithm.bounded.pipeline

import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.algorithm.bounded.BoundedChecker
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.passes.BoundMEPass
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.passes.PredicateAbstractionMEPass
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.passes.ReverseMEPass
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.passes.TraceChangeCheckMEPass
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceFwBinItpChecker
import hu.bme.mit.theta.analysis.pred.PredPrec
import hu.bme.mit.theta.common.logging.ConsoleLogger
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.*
import hu.bme.mit.theta.core.type.anytype.Exprs
import hu.bme.mit.theta.core.type.anytype.Exprs.Prime
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Not
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory
import org.junit.Assert
import org.junit.Test
import org.junit.jupiter.api.Test

class PipelineTests {

  companion object {
    private val x_var: VarDecl<IntType> = Decls.Var("x", IntType.getInstance())
    val x: RefExpr<IntType> = Exprs.Ref(x_var)
    val logger = ConsoleLogger(Logger.Level.VERBOSE)
    val solverFactory: Z3LegacySolverFactory = Z3LegacySolverFactory.getInstance()
    private val checkerFactory = { expr: MonolithicExpr ->
      BoundedChecker(
        monolithicExpr = expr,
        bmcSolver = solverFactory.createSolver(),
        itpSolver = solverFactory.createItpSolver(),
        imcEnabled = { false },
        logger = logger,
      )
    }
  }

  @Test
  fun `Single ReverseMonolithicExprPass`() {
    val expression =
      MonolithicExpr(
        initExpr = Eq(x, Int(0)),
        transExpr = Eq(Prime(x), Add(Int(1), x)),
        propExpr = Not(Eq(x, Int(3))),
      )

    val checker = checkerFactory(expression)

    val safetyResult: SafetyResult<*, *> = checker.check()
    Assert.assertTrue(safetyResult.isUnsafe())

    val pipeline =
      MonolithicExprPassPipelineChecker(
        model = expression,
        checkerFactory = checkerFactory,
        logger = logger,
      )
    pipeline.insertLastPass(ReverseMEPass())
    val pipelineResult = pipeline.check()

    Assert.assertTrue(safetyResult.isUnsafe())
    val regularCex = safetyResult.asUnsafe().cex
    val pipelineCex = pipelineResult.asUnsafe().cex
    Assert.assertEquals(regularCex.length(), pipelineCex.length())
    val states = (regularCex as Trace<*, *>).states
    val pipelineStates = (pipelineCex as Trace<*, *>).states
    for (i in states.indices) {
      Assert.assertEquals(states[i], pipelineStates[i])
    }
  }

  @Test
  fun `Complex pipeline`() {
    val expression =
      MonolithicExpr(
        initExpr = Eq(x, Int(0)),
        transExpr = Eq(Prime(x), Ite<Type>(Lt(x, Int(5)), Add(Int(1), x), x)),
        propExpr = Lt(x, Int(6)),
      )
    val initPrec = PredPrec.of(Gt(x, Int(0)))
    val traceCheckerFactory = { model: MonolithicExpr ->
      ExprTraceFwBinItpChecker.create(
        model.initExpr,
        Not(model.propExpr),
        solverFactory.createItpSolver(),
      )
    }

    val pipeline =
      MonolithicExprPassPipelineChecker(model = expression, checkerFactory = checkerFactory)
    pipeline.insertLastPass(
      PredicateAbstractionMEPass(traceCheckerFactory, { _ -> initPrec }) { prec, expr ->
        prec.join(PredPrec.of(expr))
      }
    )
    pipeline.insertLastPass(ReverseMEPass())
    pipeline.insertLastPass(TraceChangeCheckMEPass())
    pipeline.insertPass(BoundMEPass(6), 2)
    val pipelineResult = pipeline.check()
    Assert.assertTrue(pipelineResult.isSafe())
  }
}
