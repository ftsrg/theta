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
package hu.bme.mit.theta.xcfa.dss.analysis

import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.Stmts.Assign
import hu.bme.mit.theta.core.stmt.Stmts.Assume
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.inttype.IntExprs.*
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.solver.SolverManager
import hu.bme.mit.theta.xcfa.cli.checkers.getCegarChecker
import hu.bme.mit.theta.xcfa.cli.params.getDefaultPredCegarConfig
import hu.bme.mit.theta.xcfa.cli.utils.ensureDefaultSolversRegistered
import hu.bme.mit.theta.xcfa.dss.decomposition.LinearBlockDecomposition
import hu.bme.mit.theta.xcfa.dss.decomposition.SelfLoopAbsorbingDecomposition
import hu.bme.mit.theta.xcfa.model.*
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertFalse
import org.junit.jupiter.api.Assertions.assertNotEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.BeforeAll
import org.junit.jupiter.api.Test

/**
 * The CPAchecker-derived pieces of the block analysis: violation conditions, predicate operators,
 * precision combination, and [extractBlockXcfa]'s loop-head entry/exit split.
 */
class ViolationConditionTest {

  companion object {

    @JvmStatic
    @BeforeAll
    fun registerSolvers() {
      ensureDefaultSolversRegistered(getDefaultPredCegarConfig(), NullLogger.getInstance())
    }
  }

  private val operators by lazy { DssPredicateOperators(SolverManager.resolveSolverFactory("Z3")) }

  private fun check(xcfa: XCFA) =
    runWorkerConfig(
      xcfa,
      checkerFactory = { x ->
        getCegarChecker(
          x,
          emptySet(),
          ParseContext(),
          getDefaultPredCegarConfig(),
          NullLogger.getInstance(),
        )
      },
    )

  /** init -> head; head -> body -> head (x += 1, havoc y); head -> exit (x >= 10); exit -> err. */
  private fun loopProcedure(): XcfaProcedure =
    xcfa("vc-loop") {
        val main =
          procedure("main") {
            "x" type Int()
            "y" type Int()
            (init to "head") { "x" assign "0" }
            ("head" to "body") { assume("(< x 10)") }
            ("body" to "head") {
              "x" assign "(+ x 1)"
              havoc("y")
            }
            ("head" to "exit") { assume("(>= x 10)") }
            ("exit" to err) { assume("(> y x)") }
          }
        main.start()
      }
      .procedures
      .single()

  @Suppress("UNCHECKED_CAST")
  private fun XcfaProcedure.intVar(name: String) =
    vars.single { it.name == name } as VarDecl<IntType>

  @Test
  fun `the violation condition of a block with an own error is its path condition`() {
    val procedure = loopProcedure()
    val blockGraph = LinearBlockDecomposition().decompose(procedure)
    val errorBlock = blockGraph.blocks.single { block -> block.locations.any { it.error } }

    val vc =
      computeViolationCondition(
        errorBlock,
        errorBlock.locations.filter { it.error }.associateWith { True() },
      )

    val x = procedure.intVar("x").ref
    val y = procedure.intVar("y").ref
    assertTrue(operators.isLeq(vc, And(Geq(x, Int(10)), Gt(y, x))))
    assertTrue(operators.isLeq(And(Geq(x, Int(10)), Gt(y, x)), vc))
  }

  @Test
  fun `a havoc becomes an existential auxiliary variable, named canonically`() {
    val procedure = loopProcedure()
    val blockGraph = LinearBlockDecomposition().decompose(procedure)
    val body = blockGraph.blocks.single { it.initialLocation == it.finalLocation }
    val x = procedure.intVar("x").ref
    val y = procedure.intVar("y").ref
    val received = Gt(y, x)

    val vc1 = computeViolationCondition(body, mapOf(body.finalLocation to received))
    val vc2 = computeViolationCondition(body, mapOf(body.finalLocation to received))

    // wp(x < 10; x := x + 1; havoc y, y > x) = x < 10 && exists a. a > x + 1
    assertEquals(1, DssAuxVars.collectVars(vc1).size)
    assertFalse(operators.isUnsat(vc1))
    assertTrue(operators.isUnsat(And(vc1, Geq(x, Int(10)))))
    // repeated computations are structurally equal, so DSS can recognize repeated conditions
    assertEquals(vc1, vc2)
    // and passing it through the loop body again does not capture the existing variable
    val vc3 = computeViolationCondition(body, mapOf(body.finalLocation to And(vc1, Gt(y, x))))
    assertEquals(2, DssAuxVars.collectVars(vc3).size)
    assertNotEquals(vc1, vc3)
  }

  @Test
  fun `only a block that contains a whole loop has an internal cycle`() {
    val procedure = loopProcedure()
    val linear = LinearBlockDecomposition().decompose(procedure)
    assertTrue(linear.blocks.none(::hasInternalCycle), "a loop-body block is split at its head")

    val absorbed = SelfLoopAbsorbingDecomposition().decompose(procedure)
    val loopBlock = absorbed.blocks.single { block -> block.locations.any { it.name == "body" } }
    assertTrue(hasInternalCycle(loopBlock))
  }

  @Test
  fun `the path violation condition unrolls exactly the iterations of the path`() {
    val procedure = loopProcedure()
    val x = procedure.intVar("x")
    val iteration =
      listOf(StmtLabel(Assume(Lt(x.ref, Int(2)))), StmtLabel(Assign(x, Add(x.ref, Int(1)))))
    val path = iteration + iteration + StmtLabel(Assume(Geq(x.ref, Int(2))))

    val vc = computePathViolationCondition(path)

    // x < 2 && x + 1 < 2 && x + 2 >= 2, i.e., exactly two iterations from x = 0
    assertTrue(operators.isLeq(vc, Eq(x.ref, Int(0))))
    assertTrue(operators.isLeq(Eq(x.ref, Int(0)), vc))
  }

  @Test
  fun `a loop-body block analyzes exactly one iteration from its precondition`() {
    val procedure = loopProcedure()
    val blockGraph = LinearBlockDecomposition().decompose(procedure)
    val body = blockGraph.blocks.single { it.initialLocation == it.finalLocation }
    val x = procedure.intVar("x").ref

    fun reachesExitWith(value: Int): Boolean {
      val extraction =
        extractBlockXcfa(
          procedure,
          body,
          precondition = Eq(x, Int(0)),
          violationCondition = Eq(x, Int(value)),
        )
      assertNotEquals(extraction.entryLocation, extraction.exitLocation)
      return check(extraction.xcfa).isUnsafe
    }

    assertFalse(reachesExitWith(0), "the entry state must not count as a block-end state")
    assertTrue(reachesExitWith(1))
    assertFalse(reachesExitWith(2), "a block analysis must not iterate the body twice")
  }

  @Test
  fun `a violation condition attached to the block exit makes the block unsafe exactly when it is reachable`() {
    val procedure = loopProcedure()
    val blockGraph = LinearBlockDecomposition().decompose(procedure)
    val root = blockGraph.root
    val x = procedure.intVar("x").ref

    val reachable = extractBlockXcfa(procedure, root, violationCondition = Eq(x, Int(0)))
    val unreachable = extractBlockXcfa(procedure, root, violationCondition = Eq(x, Int(5)))

    assertTrue(check(reachable.xcfa).isUnsafe)
    assertTrue(check(unreachable.xcfa).isSafe)
  }

  @Test
  fun `predicate precisions are combined like CPAchecker's CombinePredicatePrecisionOperator`() {
    val procedure = loopProcedure()
    val x = procedure.intVar("x").ref
    val y = procedure.intVar("y").ref
    val p1 = setOf(Lt(x, Int(10)), Gt(y, Int(0)))
    val p2 = setOf(Geq(x, Int(3)))

    // x occurs in both precisions, so only predicates over x are kept
    assertEquals(setOf(Lt(x, Int(10)), Geq(x, Int(3))), combinePredPrecs(listOf(p1, p2)))
    // no common variable: plain union
    val p3 = setOf(Gt(y, Int(1)))
    assertEquals(p2 + p3, combinePredPrecs(listOf(p2, p3)))
  }
}
