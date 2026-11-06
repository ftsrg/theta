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

import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Not
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Or
import hu.bme.mit.theta.core.type.inttype.IntExprs.*
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.solver.SolverManager
import hu.bme.mit.theta.xcfa.analysis.dss.ensureDefaultSolversRegistered
import hu.bme.mit.theta.xcfa.cli.params.getDefaultPredCegarConfig
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertNull
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.BeforeAll
import org.junit.jupiter.api.Test

class ViolationGeneralizationTest {

  companion object {
    @JvmStatic
    @BeforeAll
    fun registerSolvers() {
      ensureDefaultSolversRegistered(getDefaultPredCegarConfig(), NullLogger.getInstance())
    }
  }

  private val operators by lazy { DssPredicateOperators(SolverManager.resolveSolverFactory("Z3")) }

  private val x = Var("x", Int())
  private val y = Var("y", Int())
  private val n = Var("n", Int())
  private val flag = Var("flag", Bool())

  private fun equivalent(a: Expr<BoolType>, b: Expr<BoolType>) =
    operators.isLeq(a, b) && operators.isLeq(b, a)

  private fun generalize(
    conditions: List<Expr<BoolType>>,
    generalizer: ViolationGeneralizer = ViolationGeneralizer(gas = 2),
  ): ViolationGeneralizer.Generalization? {
    conditions.forEach { generalizer.record("B", it) }
    return generalizer.generalize(listOf("B" to conditions.last()), operators::isUnsat)
  }

  /** The exact weakest precondition of `k` iterations of `x := x + 1` before `x == -1`. */
  private fun errorInLoopCondition(k: Int): Expr<BoolType> =
    And(
      (0..k).map { j -> Lt(Add(x.ref, Int(j)), n.ref) } +
        (1..k).map { j -> Neq(Add(x.ref, Int(j)), Int(-1)) } +
        Eq(Add(x.ref, Int(k + 1)), Int(-1))
    )

  @Test
  fun `equalities are substituted and implied bounds dropped`() {
    val cube = normalizedCubes(errorInLoopCondition(2))!!.single()
    assertEquals(2, cube.linear.size, cube.toExpr().toString())
    assertTrue(cube.opaque.isEmpty(), cube.toExpr().toString())
    assertTrue(equivalent(cube.toExpr(), And(Eq(x.ref, Int(-4)), Geq(n.ref, Int(-1)))))
  }

  @Test
  fun `a contradictory cube is dropped`() {
    assertEquals(emptyList<Cube>(), normalizedCubes(And(Eq(x.ref, Int(1)), Lt(x.ref, Int(0)))))
  }

  @Test
  fun `the unrolled loop condition generalizes to its unbounded hull`() {
    val conditions = (0..2).map(::errorInLoopCondition)
    val generalization = requireNotNull(generalize(conditions))
    // x = -2 - t for t >= 0, with the stable bound n >= -1
    assertTrue(
      equivalent(generalization.condition, And(Leq(x.ref, Int(-2)), Geq(n.ref, Int(-1)))),
      generalization.condition.toString(),
    )
    conditions.forEach { assertTrue(operators.isLeq(it, generalization.condition)) }
  }

  @Test
  fun `a drift in two coupled bounds keeps their relation`() {
    // Backward conditions of the guarded loop: the entry reaches x == k with n >= k
    val conditions = (0..2).map { k -> And(Eq(x.ref, Int(k)), Geq(n.ref, x.ref)) }
    val generalization = requireNotNull(generalize(conditions))
    assertTrue(
      equivalent(generalization.condition, And(Geq(x.ref, Int(0)), Leq(x.ref, n.ref))),
      generalization.condition.toString(),
    )
  }

  @Test
  fun `a chain of auxiliary variables is solved and leaves no literal behind`() {
    // The backward guarded loop: x = a0 + 1, a0 = a1 + 1, ..., a(k-1) = 0, each ai < n
    @Suppress("UNCHECKED_CAST") fun aux(i: Int) = (DssAuxVars.of(i, Int()) as VarDecl<IntType>).ref
    fun condition(k: Int) =
      And(
        listOf(Eq(x.ref, Add(aux(0), Int(1))), Geq(n.ref, Int(0)), Eq(aux(k - 1), Int(0))) +
          (0 until k).map { Lt(aux(it), n.ref) } +
          (0 until k - 1).map { Eq(aux(it), Add(aux(it + 1), Int(1))) }
      )
    val cubes = (1..3).map { normalizedCubes(condition(it))!!.single() }
    assertTrue(cubes.all { it.shape == cubes[0].shape }, cubes.map { it.toExpr() }.toString())
    val generalization = requireNotNull(generalize((1..3).map(::condition)))
    assertTrue(
      equivalent(generalization.condition, And(Geq(x.ref, Int(1)), Leq(x.ref, n.ref))),
      generalization.condition.toString(),
    )
  }

  @Test
  fun `dependent bounds become one parameter (the paper's Example 4)`() {
    val conditions = listOf(2, 4, 8).map { k -> And(Eq(x.ref, Int(k)), Leq(y.ref, Int(k + 1))) }
    val generalization = requireNotNull(generalize(conditions))
    assertTrue(
      equivalent(generalization.condition, And(Geq(x.ref, Int(2)), Leq(y.ref, Add(x.ref, Int(1))))),
      generalization.condition.toString(),
    )
  }

  @Test
  fun `without a monotone drift the drifting literals are dropped`() {
    val conditions =
      listOf(1, 3, 2).map { k -> And(Eq(x.ref, Int(k)), Leq(y.ref, Int(5)), flag.ref) }
    val generalization = requireNotNull(generalize(conditions))
    assertTrue(
      equivalent(generalization.condition, And(Leq(y.ref, Int(5)), flag.ref)),
      generalization.condition.toString(),
    )
  }

  @Test
  fun `a single condition or a stable cluster is not generalized`() {
    assertNull(generalize(listOf(errorInLoopCondition(0))))
    assertNull(generalize(listOf(Eq(x.ref, Int(1)), Eq(x.ref, Int(1)))))
    assertNull(generalize(listOf(flag.ref, Not(flag.ref))))
  }

  @Test
  fun `clusters are kept per sender`() {
    val generalizer = ViolationGeneralizer(gas = 2)
    generalizer.record("A", Eq(x.ref, Int(1)))
    generalizer.record("B", Eq(x.ref, Int(2)))
    assertNull(generalizer.generalize(listOf("B" to Eq(x.ref, Int(2))), operators::isUnsat))
  }

  @Test
  fun `a failed candidate is replaced, and a cluster out of gas is no longer generalized`() {
    val generalizer = ViolationGeneralizer(gas = 2)
    val conditions = (0..2).map(::errorInLoopCondition)
    val first = requireNotNull(generalize(conditions, generalizer))
    generalizer.failed(first)
    val received = listOf("B" to conditions.last())
    val second = requireNotNull(generalizer.generalize(received, operators::isUnsat))
    // The hull failed: the cube without its drifting literal, n >= -1
    assertTrue(equivalent(second.condition, Geq(n.ref, Int(-1))), second.condition.toString())
    generalizer.failed(second)
    assertNull(generalizer.generalize(received, operators::isUnsat))
  }

  @Test
  fun `every disjunct of a path condition is clustered`() {
    val conditions = (0..2).map { k -> Or((0..k).map(::errorInLoopCondition)) }
    val generalization = requireNotNull(generalize(conditions))
    assertTrue(
      equivalent(generalization.condition, And(Leq(x.ref, Int(-2)), Geq(n.ref, Int(-1)))),
      generalization.condition.toString(),
    )
  }
}
