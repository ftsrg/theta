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
package hu.bme.mit.theta.analysis.algorithm

import hu.bme.mit.theta.analysis.algorithm.bounded.BoundedChecker
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr
import hu.bme.mit.theta.common.logging.ConsoleLogger
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.stmt.Stmts.Assign
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.inttype.IntExprs
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.utils.StmtUtils
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory
import org.junit.Assert
import org.junit.Test

class BoundedTest {

  companion object {

    private var unsafeMonolithicExpr: MonolithicExpr? = null
    private var safeMonolithicExpr: MonolithicExpr? = null
    private val valToState = { valuation: Valuation -> ExprStateStub(valuation.toExpr()) }
    private val biValToAction = { valuation: Valuation?, valuation2: Valuation? ->
      ExprActionStub(emptyList())
    }

    init {
      val x = Decls.Var("x", Int())
      val unfoldResult =
        StmtUtils.toExpr(Assign(x, IntExprs.Add(x.ref, Int(1))), VarIndexingFactory.indexing(0))
      unsafeMonolithicExpr =
        MonolithicExpr(
          AbstractExprs.Eq(x.ref, Int(0)),
          And(unfoldResult.exprs),
          AbstractExprs.Neq(x.ref, Int(5)),
          unfoldResult.indexing,
        )
      safeMonolithicExpr =
        MonolithicExpr(
          AbstractExprs.Eq(x.ref, Int(0)),
          And(unfoldResult.exprs),
          AbstractExprs.Neq(x.ref, Int(-5)),
          unfoldResult.indexing,
        )
    }
  }

  @Test
  fun testBoundedUnsafe() {
    val solver = Z3LegacySolverFactory.getInstance().createSolver()
    val itpSolver = Z3LegacySolverFactory.getInstance().createItpSolver()
    val indSolver = Z3LegacySolverFactory.getInstance().createSolver()
    val fpSolver = Z3LegacySolverFactory.getInstance().createSolver()
    val checker: BoundedChecker<*, *> =
      BoundedChecker(
        monolithicExpr = unsafeMonolithicExpr!!,
        bmcSolver = solver,
        itpSolver = itpSolver,
        imcFpSolver = fpSolver,
        indSolver = indSolver,
        valToState = valToState,
        biValToAction = biValToAction,
        logger = ConsoleLogger(Logger.Level.VERBOSE),
      )
    val safetyResult: SafetyResult<*, *> = checker.check()
    Assert.assertTrue(safetyResult.isUnsafe())
  }

  @Test
  fun testBoundedSafe() {
    val solver = Z3LegacySolverFactory.getInstance().createSolver()
    val itpSolver = Z3LegacySolverFactory.getInstance().createItpSolver()
    val indSolver = Z3LegacySolverFactory.getInstance().createSolver()
    val fpSolver = Z3LegacySolverFactory.getInstance().createSolver()
    val checker: BoundedChecker<*, *> =
      BoundedChecker(
        monolithicExpr = safeMonolithicExpr!!,
        bmcSolver = solver,
        itpSolver = itpSolver,
        imcFpSolver = fpSolver,
        indSolver = indSolver,
        valToState = valToState,
        biValToAction = biValToAction,
        logger = ConsoleLogger(Logger.Level.VERBOSE),
      )
    val safetyResult: SafetyResult<*, *> = checker.check()
    Assert.assertTrue(safetyResult.isSafe())
  }
}
