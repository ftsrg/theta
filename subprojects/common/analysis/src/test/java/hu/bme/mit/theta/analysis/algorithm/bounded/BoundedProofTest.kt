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

import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.stmt.NonDetStmt
import hu.bme.mit.theta.core.stmt.SequenceStmt
import hu.bme.mit.theta.core.stmt.Stmt
import hu.bme.mit.theta.core.stmt.Stmts.Assign
import hu.bme.mit.theta.core.stmt.Stmts.Assume
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Geq
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Lt
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Neq
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.inttype.IntExprs.Add
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.PathUtils
import hu.bme.mit.theta.core.utils.StmtUtils
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertFalse
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

/**
 * Location 0 reaches the final location 2 directly (`y := 1`) or through a loop at 1 (`y := 2`);
 * location 3 is the error, entered from 2 if `y == 3`. The direct path is shorter than k and cannot
 * be extended, so a proof that asks for k-step paths through each state loses its end state.
 */
class BoundedProofTest {

  private val l = Var("l", Int())
  private val i = Var("i", Int())
  private val y = Var("y", Int())

  private fun edge(from: Int, to: Int, guard: Expr<BoolType>, vararg updates: Stmt): Stmt =
    SequenceStmt.of(
      listOf(Assume(Eq(l.ref, Int(from))), Assume(guard)) + updates + Assign(l, Int(to))
    )

  private fun model(withLoop: Boolean): MonolithicExpr {
    val edges =
      listOfNotNull(
        edge(0, 2, True(), Assign(y, Int(1))),
        edge(0, 1, True(), Assign(i, Int(0)), Assign(y, Int(0))),
        if (withLoop) edge(1, 1, Lt(i.ref, Int(10)), Assign(i, Add(i.ref, Int(1)))) else null,
        edge(1, 2, if (withLoop) Geq(i.ref, Int(10)) else True(), Assign(y, Int(2))),
        edge(2, 3, Eq(y.ref, Int(3))),
      )
    val unfolded = StmtUtils.toExpr(NonDetStmt.of(edges), VarIndexingFactory.indexing(0))
    return MonolithicExpr(
      initExpr = Eq(l.ref, Int(0)),
      transExpr = And(unfolded.exprs),
      propExpr = Neq(l.ref, Int(3)),
      transOffsetIndex = unfolded.indexing,
    )
  }

  private fun proofOf(model: MonolithicExpr, kind: Boolean, interpolate: Boolean): Expr<BoolType> {
    val factory = Z3LegacySolverFactory.getInstance()
    val result =
      BoundedChecker(
          monolithicExpr = model,
          bmcSolver = factory.createSolver(),
          itpSolver = factory.createItpSolver(),
          imcEnabled = { false },
          indSolver = factory.createSolver(),
          kindEnabled = { kind },
          logger = NullLogger.getInstance(),
          needProof = true,
          interpolateProof = interpolate,
        )
        .check()
    assertTrue(result.isSafe) { "$result" }
    return result.asSafe().proof.toExpr()
  }

  /** Free variables of [proof] other than the model's are existential. */
  private fun admits(proof: Expr<BoolType>, state: Expr<BoolType>): Boolean {
    val solver = Z3LegacySolverFactory.getInstance().createSolver()
    solver.add(PathUtils.unfold(And(proof, state), 0))
    return solver.check().isSat
  }

  private val shortcutEnd = And(Eq(l.ref, Int(2)), Eq(y.ref, Int(1)))
  private val loopEnd = And(Eq(l.ref, Int(2)), Eq(y.ref, Int(2)))
  private val beforeError = And(Eq(l.ref, Int(2)), Eq(y.ref, Int(3)))

  @Test
  fun `the proof of the loop-freeness check covers ends of shorter paths`() {
    for (interpolate in listOf(false, true)) {
      val proof = proofOf(model(withLoop = false), kind = false, interpolate = interpolate)
      assertTrue(admits(proof, shortcutEnd)) { "$proof" }
      assertTrue(admits(proof, loopEnd)) { "$proof" }
    }
  }

  @Test
  fun `the k-induction proof covers ends of paths shorter than k`() {
    for (interpolate in listOf(false, true)) {
      val proof = proofOf(model(withLoop = true), kind = true, interpolate = interpolate)
      assertTrue(admits(proof, shortcutEnd)) { "$proof" }
      assertTrue(admits(proof, loopEnd)) { "$proof" }
    }
  }

  @Test
  fun `an interpolated proof is over the model's variables and excludes states before an error`() {
    for (kind in listOf(false, true)) {
      val proof = proofOf(model(withLoop = kind), kind = kind, interpolate = true)
      assertTrue(ExprUtils.getVars(proof).all { it in setOf(l, i, y) }) { "$proof" }
      assertFalse(admits(proof, beforeError)) { "$proof" }
      assertFalse(admits(proof, Eq(l.ref, Int(3)))) { "$proof" }
    }
  }

  @Test
  fun `existential proofs of different runs share no variables`() {
    val first = proofOf(model(withLoop = true), kind = true, interpolate = false)
    val second = proofOf(model(withLoop = true), kind = true, interpolate = false)
    val fresh = { proof: Expr<BoolType> -> ExprUtils.getVars(proof) - setOf(l, i, y) }
    assertTrue(fresh(first).isNotEmpty())
    assertEquals(emptySet<Any>(), fresh(first) intersect fresh(second))
  }
}
