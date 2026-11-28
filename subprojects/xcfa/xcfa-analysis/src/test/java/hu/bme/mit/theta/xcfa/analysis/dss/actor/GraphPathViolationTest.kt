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
package hu.bme.mit.theta.xcfa.analysis.dss.actor

import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Or
import hu.bme.mit.theta.core.type.inttype.IntExprs.Gt
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntExprs.Lt
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.solver.SolverManager
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.DssCheckerRoster
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.DssPredicateOperators
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.DssViolationConditions
import hu.bme.mit.theta.xcfa.analysis.dss.decomposition.SingleBlockDecomposition
import hu.bme.mit.theta.xcfa.analysis.dss.ensureDefaultSolversRegistered
import hu.bme.mit.theta.xcfa.cli.checkers.getCegarChecker
import hu.bme.mit.theta.xcfa.cli.params.Refinement
import hu.bme.mit.theta.xcfa.cli.params.getDefaultPredCegarConfig
import hu.bme.mit.theta.xcfa.model.*
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertFalse
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.BeforeAll
import org.junit.jupiter.api.Test

/** `--dss-violation-conditions GRAPH_PATHS`: a condition per feasible target of the CEGAR graph. */
class GraphPathViolationTest {

  companion object {

    @JvmStatic
    @BeforeAll
    fun registerSolvers() {
      ensureDefaultSolversRegistered(getDefaultPredCegarConfig(), NullLogger.getInstance())
    }
  }

  private val operators by lazy { DssPredicateOperators(SolverManager.resolveSolverFactory("Z3")) }

  private fun roster(refinement: Refinement, keepProofTree: Boolean) =
    DssCheckerRoster(
      listOf { x ->
        getCegarChecker(
          x,
          emptySet(),
          ParseContext(),
          getDefaultPredCegarConfig(refinement = refinement),
          NullLogger.getInstance(),
          keepProofTree = keepProofTree,
        )
      }
    )

  /** x is unconstrained at the start; `x > 5` and `x < -5` lead to the error on separate paths. */
  private val twoErrors: XCFA =
    xcfa("graph-two-errors") {
      val main =
        procedure("main") {
          "x" type Int()
          (init to "a") { nop() }
          ("a" to "high") { assume("(> x 5)") }
          ("a" to "low") { assume("(< x (- 5))") }
          ("a" to final) { assume("(and (<= x 5) (>= x (- 5)))") }
          ("high" to err) { nop() }
          ("low" to err) { nop() }
        }
      main.start()
    }

  /** As [twoErrors], but the `x > 5` path is infeasible: `x < 3` follows it. */
  private val oneSpurious: XCFA =
    xcfa("graph-one-spurious") {
      val main =
        procedure("main") {
          "x" type Int()
          (init to "a") { nop() }
          ("a" to "high") { assume("(> x 5)") }
          ("high" to "check") { nop() }
          ("check" to err) { assume("(< x 3)") }
          ("a" to "low") { assume("(< x (- 5))") }
          ("low" to err) { nop() }
        }
      main.start()
    }

  @Suppress("UNCHECKED_CAST")
  private fun XCFA.intVar(name: String) =
    procedures.single().vars.single { it.name == name } as VarDecl<IntType>

  private fun equivalent(a: Expr<BoolType>, b: Expr<BoolType>) =
    operators.isLeq(a, b) && operators.isLeq(b, a)

  private fun initialAnalysis(
    program: XCFA,
    mode: DssViolationConditions,
    refinement: Refinement = Refinement.MULTI_SEQ,
    keepProofTree: Boolean = true,
  ): Pair<Expr<BoolType>, Map<String, String>> {
    val procedure = program.procedures.single()
    val block = SingleBlockDecomposition.decompose(procedure).root
    val behavior =
      PredicateBlockBehavior(
        program,
        procedure,
        block,
        roster(refinement, keepProofTree),
        // The program's assumptions as predicates would refute the spurious path abstractly
        useGlobalPredicatePool = false,
        violationConditionMode = mode,
      )
    val messages = behavior.runInitialAnalysis()
    val vc = messages.filterIsInstance<DssViolationConditionMessage>().single().violationCondition!!
    return vc to behavior.statistics()
  }

  @Test
  fun `one fully explored run sends the conditions of both error paths`() {
    val x = twoErrors.intVar("x").ref
    val both = Or(Gt(x, Int(5)), Lt(x, Int(-5)))

    val (graph, stats) = initialAnalysis(twoErrors, DssViolationConditions.GRAPH_PATHS)
    val (allPaths, _) = initialAnalysis(twoErrors, DssViolationConditions.ALL_PATHS)

    assertTrue(equivalent(graph, both), "GRAPH_PATHS: $graph")
    assertTrue(equivalent(graph, allPaths), "GRAPH_PATHS $graph, ALL_PATHS $allPaths")
    assertEquals("2", stats["graphPaths"], "$stats")
  }

  @Test
  fun `per-path conditions from the counterexample alone send one of the paths`() {
    val x = twoErrors.intVar("x").ref
    val both = Or(Gt(x, Int(5)), Lt(x, Int(-5)))

    val (paths, _) = initialAnalysis(twoErrors, DssViolationConditions.PATHS)

    assertTrue(operators.isLeq(paths, both), "PATHS: $paths")
    assertFalse(operators.isLeq(both, paths), "PATHS: $paths")
  }

  @Test
  fun `a spurious target of the graph is dropped`() {
    val x = oneSpurious.intVar("x").ref

    val (graph, stats) = initialAnalysis(oneSpurious, DssViolationConditions.GRAPH_PATHS)

    assertTrue(equivalent(graph, Lt(x, Int(-5))), "GRAPH_PATHS: $graph")
    assertEquals("1", stats["graphPathsInfeasible"], "$stats")
  }

  @Test
  fun `without a kept graph, GRAPH_PATHS sends the counterexample's path`() {
    val x = twoErrors.intVar("x").ref
    val both = Or(Gt(x, Int(5)), Lt(x, Int(-5)))

    val (graph, stats) =
      initialAnalysis(twoErrors, DssViolationConditions.GRAPH_PATHS, keepProofTree = false)

    assertTrue(operators.isLeq(graph, both), "GRAPH_PATHS: $graph")
    assertFalse(operators.isLeq(both, graph), "GRAPH_PATHS: $graph")
    assertEquals("0", stats["graphPaths"], "$stats")
  }
}
