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
package hu.bme.mit.theta.xcfa.cli.utils

import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.stmt.MemoryAssignStmt
import hu.bme.mit.theta.core.stmt.Stmts.Assign
import hu.bme.mit.theta.core.stmt.Stmts.Assume
import hu.bme.mit.theta.core.stmt.Stmts.Havoc
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.inttype.IntExprs.Add
import hu.bme.mit.theta.core.type.inttype.IntExprs.Geq
import hu.bme.mit.theta.core.type.inttype.IntExprs.Gt
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntExprs.Leq
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.xcfa.model.StmtLabel
import hu.bme.mit.theta.xcfa.model.XcfaLabel
import java.math.BigInteger
import org.junit.jupiter.api.Assertions.assertFalse
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

class OverApproximationGuardTest {

  private val n = Var("n", Int())
  private val k = Var("k", Int())
  private val x = Var("x", Int())
  private val intRange = BigInteger.TWO.pow(31).negate()..BigInteger.TWO.pow(31).dec()
  private val recorded = mapOf("n" to intRange)
  private val cell: Dereference<IntType, IntType, IntType> = Dereference.of(Int(13), Int(0), Int())

  private fun assume(cond: Expr<BoolType>): XcfaLabel = StmtLabel(Assume(cond))

  private fun range(lo: BigInteger, hi: BigInteger): XcfaLabel =
    assume(And(Geq(n.ref, Int(lo)), Leq(n.ref, Int(hi))))

  private fun typeRange() = range(intRange.start, intRange.endInclusive)

  @Test
  fun `a recorded value that no assumption reads does not decide the trace`() {
    val labels =
      listOf(StmtLabel(Havoc(n)), typeRange(), StmtLabel(Havoc(k)), assume(Gt(k.ref, Int(5))))
    assertFalse(dependsOnOverApproximation(labels, recorded))
  }

  @Test
  fun `an assumption on the recorded value decides the trace`() {
    val labels = listOf(StmtLabel(Havoc(n)), typeRange(), assume(Gt(n.ref, Int(100))))
    assertTrue(dependsOnOverApproximation(labels, recorded))
  }

  @Test
  fun `a range narrower than the type is an assumption on the value`() {
    val labels = listOf(StmtLabel(Havoc(n)), range(BigInteger.ZERO, BigInteger.valueOf(255)))
    assertTrue(dependsOnOverApproximation(labels, recorded))
  }

  @Test
  fun `a recorded value that reaches an assumption through an assignment decides the trace`() {
    val labels =
      listOf(
        StmtLabel(Havoc(n)),
        typeRange(),
        StmtLabel(Assign(x, Add(n.ref, Int(1)))),
        assume(Gt(x.ref, Int(0))),
      )
    assertTrue(dependsOnOverApproximation(labels, recorded))
  }

  @Test
  fun `a recorded value that is stored and read back decides the trace`() {
    val labels =
      listOf(
        StmtLabel(Havoc(n)),
        typeRange(),
        StmtLabel(MemoryAssignStmt.create(cell, n.ref)),
        StmtLabel(Assign(x, cell)),
        assume(Gt(x.ref, Int(0))),
      )
    assertTrue(dependsOnOverApproximation(labels, recorded))
  }

  @Test
  fun `a store after the last read of memory does not decide the trace`() {
    val labels =
      listOf(
        StmtLabel(Havoc(n)),
        typeRange(),
        StmtLabel(Assign(x, cell)),
        assume(Gt(x.ref, Int(0))),
        StmtLabel(MemoryAssignStmt.create(cell, n.ref)),
      )
    assertFalse(dependsOnOverApproximation(labels, recorded))
  }

  @Test
  fun `a recorded fact about the value does not decide the trace`() {
    val fact = And(Geq(n.ref, x.ref), Leq(n.ref, Int(1)))
    val labels = listOf(StmtLabel(Havoc(n)), assume(fact), assume(Gt(x.ref, Int(0))))
    assertFalse(dependsOnOverApproximation(labels, recorded) { it == fact })
    assertTrue(dependsOnOverApproximation(labels, recorded))
  }

  @Test
  fun `a recorded value used beyond its facts still decides the trace`() {
    val fact = Leq(n.ref, Int(1))
    val labels = listOf(StmtLabel(Havoc(n)), assume(fact), assume(Gt(n.ref, Int(0))))
    assertTrue(dependsOnOverApproximation(labels, recorded) { it == fact })
  }
}
