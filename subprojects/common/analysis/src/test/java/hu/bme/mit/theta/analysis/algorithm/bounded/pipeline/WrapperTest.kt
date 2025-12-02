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

import hu.bme.mit.theta.analysis.algorithm.bounded.BoundedChecker
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.passes.ReverseMEPass
import hu.bme.mit.theta.common.logging.ConsoleLogger
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.*
import hu.bme.mit.theta.core.type.anytype.Exprs
import hu.bme.mit.theta.core.type.anytype.Exprs.Prime
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory
import org.junit.jupiter.api.Test

class WrapperTest {

  companion object {
    private val x_var: VarDecl<IntType> = Decls.Var("x", IntType.getInstance())
    val x: RefExpr<IntType> = Exprs.Ref(x_var)
    private val logger = ConsoleLogger(Logger.Level.VERBOSE)
    private val solverFactory: Z3LegacySolverFactory = Z3LegacySolverFactory.getInstance()
    private val checkerFactory = { expr: MonolithicExpr ->
      BoundedChecker(
        monolithicExpr = expr,
        bmcSolver = solverFactory.createSolver(),
        itpSolver = solverFactory.createItpSolver(),
        imcEnabled = { false },
        logger = logger,
      )
    }
    val expression =
      MonolithicExpr(
        initExpr = Eq(PipelineTests.x, Int(0)),
        transExpr =
          Eq(
            Prime(PipelineTests.x),
            Ite<Type>(Lt(PipelineTests.x, Int(5)), Add(Int(1), PipelineTests.x), PipelineTests.x),
          ),
        propExpr = Lt(PipelineTests.x, Int(6)),
      )
  }

  @Test
  fun `Wrap a reverse pass`() {
    val checker = MEPassCheckWrapper(expression, ReverseMEPass(), checkerFactory)
    val result = checker.check(null)
    assert(result.isSafe)
  }
}
