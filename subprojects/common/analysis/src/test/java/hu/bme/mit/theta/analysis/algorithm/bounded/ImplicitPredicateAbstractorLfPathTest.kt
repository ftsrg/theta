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
package hu.bme.mit.theta.analysis.algorithm.bounded

import hu.bme.mit.theta.analysis.algorithm.InvariantProof
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.MonolithicExprPassPipelineChecker
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.passes.PredicateAbstractionMEPass
import hu.bme.mit.theta.analysis.expr.refinement.createFwBinItpCheckerFactory
import hu.bme.mit.theta.analysis.pred.PredPrec
import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Add
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.anytype.Exprs.Prime
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Not
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.Timeout

/** Loop-free path checking must stay sound on models produced by implicit predicate abstraction. */
@Timeout(60)
class ImplicitPredicateAbstractorLfPathTest {

  private val solverFactory = Z3LegacySolverFactory.getInstance()
  private val logger = NullLogger.getInstance()
  private val x = Decls.Var("x", IntType.getInstance())
  private val t = Decls.Var("t", IntType.getInstance())

  // x := 0; loop { x := x + 1 }, violated after 2 steps
  private val counter =
    MonolithicExpr(
      initExpr = Eq(x.ref, Int(0)),
      transExpr = Eq(Prime(x.ref), Add(x.ref, Int(1))),
      propExpr = Not(Eq(x.ref, Int(2))),
    )

  // x := 0; loop { t := x; t := t + 1; x := t }, with t local to the transition
  private val localVar =
    MonolithicExpr(
      initExpr = Eq(x.ref, Int(0)),
      transExpr =
        And(
          Eq(Prime(t.ref), x.ref),
          Eq(Prime(Prime(t.ref)), Add(Prime(t.ref), Int(1))),
          Eq(Prime(x.ref), Prime(Prime(t.ref))),
        ),
      propExpr = Not(Eq(x.ref, Int(3))),
      transOffsetIndex = VarIndexingFactory.indexingBuilder(1).inc(t).build(),
      vars = listOf(x),
    )

  private fun check(
    model: MonolithicExpr,
    initPrec: (MonolithicExpr) -> PredPrec,
    checkerFactory: (MonolithicExpr) -> BoundedChecker,
  ) =
    MonolithicExprPassPipelineChecker<InvariantProof>(
        model,
        checkerFactory,
        mutableListOf(
          PredicateAbstractionMEPass(createFwBinItpCheckerFactory(solverFactory), initPrec)
        ),
      )
      .check(null)

  private val propOnly = { m: MonolithicExpr -> PredPrec.of(m.propExpr) }
  private val propAndInit = { m: MonolithicExpr -> PredPrec.of(listOf(m.propExpr, m.initExpr)) }

  @Test
  fun `BMC with abstract init not in the precision`() {
    val result =
      check(counter, propOnly) { m ->
        buildBMC(m, solverFactory.createSolver(), logger, { it > 20 }, { true }, { true })
      }
    assertTrue(result.isUnsafe) { "expected unsafe, got $result" }
  }

  @Test
  fun `KIND with abstract init not in the precision`() {
    val result =
      check(counter, propOnly) { m ->
        buildKIND(
          m,
          solverFactory.createSolver(),
          solverFactory.createSolver(),
          logger,
          { it > 20 },
          { true },
          { true },
        )
      }
    assertTrue(result.isUnsafe) { "expected unsafe, got $result" }
  }

  @Test
  fun `IMC with abstract init not in the precision`() {
    val result =
      check(counter, propOnly) { m ->
        buildIMC(
          m,
          solverFactory.createSolver(),
          solverFactory.createItpSolver(),
          logger,
          { it > 20 },
          { false },
          { true },
        )
      }
    assertTrue(result.isUnsafe) { "expected unsafe, got $result" }
  }

  @Test
  fun `BMC with a trans-local variable primed twice`() {
    val result =
      check(localVar, propAndInit) { m ->
        buildBMC(m, solverFactory.createSolver(), logger, { it > 30 }, { true }, { true })
      }
    assertTrue(result.isUnsafe) { "expected unsafe, got $result" }
  }
}
