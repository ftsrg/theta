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
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And
import hu.bme.mit.theta.core.type.inttype.IntExprs.*
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.solver.SolverManager
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.DssCheckerRoster
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.DssGeneralizerKind
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.DssPredicateOperators
import hu.bme.mit.theta.xcfa.analysis.dss.decomposition.LinearBlockDecomposition
import hu.bme.mit.theta.xcfa.analysis.dss.ensureDefaultSolversRegistered
import hu.bme.mit.theta.xcfa.cli.checkers.getCegarChecker
import hu.bme.mit.theta.xcfa.cli.params.getDefaultPredCegarConfig
import hu.bme.mit.theta.xcfa.model.*
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.BeforeAll
import org.junit.jupiter.api.Test

/** A root block probed with generalizations of a drifting sequence `x == 12, x == 13, ...`. */
class ViolationProbeTest {

  companion object {
    @JvmStatic
    @BeforeAll
    fun registerSolvers() {
      ensureDefaultSolversRegistered(getDefaultPredCegarConfig(), NullLogger.getInstance())
    }
  }

  private val operators by lazy { DssPredicateOperators(SolverManager.resolveSolverFactory("Z3")) }

  private val roster =
    DssCheckerRoster(
      listOf { x ->
        getCegarChecker(
          x,
          emptySet(),
          ParseContext(),
          getDefaultPredCegarConfig(),
          NullLogger.getInstance(),
        )
      }
    )

  /** init -(x := value)-> branch; branch -(x < 10)-> final; branch -(x >= 10)-> err. */
  private fun program(value: Int): XCFA =
    xcfa("probe") {
      val main =
        procedure("main") {
          "x" type Int()
          (init to "branch") { "x" assign "$value" }
          ("branch" to final) { assume("(< x 10)") }
          ("branch" to err) { assume("(>= x 10)") }
        }
      main.start()
    }

  private class Answer(val messages: List<DssMessage>, val statistics: Map<String, String>) {
    val violations = messages.filterIsInstance<DssViolationConditionMessage>()
    val postconditions = messages.filterIsInstance<DssPostConditionMessage>()
  }

  /** The root's answers to `x == first`, `x == first + 1`, ... from the error block. */
  private fun answers(
    value: Int,
    first: Int,
    count: Int,
    gas: Int,
    generalizers: List<DssGeneralizerKind> = listOf(DssGeneralizerKind.GSPACER),
  ): List<Answer> {
    val program = program(value)
    val procedure = program.procedures.single()
    val graph = LinearBlockDecomposition().decompose(procedure)
    @Suppress("UNCHECKED_CAST")
    val x = (procedure.vars.single { it.name == "x" } as VarDecl<IntType>).ref
    val sender = graph.blocks.single { b -> b.locations.any { it.error } }.id
    val root =
      PredicateBlockBehavior(
        program,
        procedure,
        graph.root,
        roster,
        generalizationGas = gas,
        generalizers = generalizers,
      )
    root.runInitialAnalysis()
    return (first until first + count).map { k ->
      val messages =
        root.onViolationCondition(DssViolationConditionMessage(sender, Eq(x, Int(k)))).toList()
      Answer(messages, root.statistics())
    }
  }

  @Test
  fun `a refuted generalization refutes the condition and strengthens the postcondition`() {
    val last = answers(value = 5, first = 12, count = 2, gas = 2).last()
    assertEquals("1", last.statistics["probesRefuted"], "${last.statistics}")
    assertEquals("0", last.statistics["probesFailed"])
    assertTrue(last.violations.isEmpty(), "${last.messages}")
    val post = last.postconditions.single().postcondition!!
    val x = ExprUtils.getVars(post).single { it.name == "x" }
    @Suppress("UNCHECKED_CAST")
    assertTrue(
      operators.isUnsat(And(post, Geq((x as VarDecl<IntType>).ref, Int(12)))),
      "the postcondition excludes the generalization x >= 12: $post",
    )
  }

  @Test
  fun `a semantic generalization is refuted from the first condition on`() {
    val semantic = listOf(DssGeneralizerKind.SEMANTIC)
    val first = answers(value = 5, first = 12, count = 1, gas = 2, generalizers = semantic).single()
    assertEquals("1", first.statistics["probesRefuted"], "${first.statistics}")
    assertTrue(first.violations.isEmpty(), "${first.messages}")
    val post = first.postconditions.single().postcondition!!
    val x = ExprUtils.getVars(post).single { it.name == "x" }
    @Suppress("UNCHECKED_CAST")
    assertTrue(
      operators.isUnsat(And(post, Geq((x as VarDecl<IntType>).ref, Int(12)))),
      "the postcondition excludes the generalization x >= 12: $post",
    )
  }

  @Test
  fun `a failed probe falls back to the exact condition`() {
    // x == 15 reaches the generalization x >= 12, but not x == 13
    val last = answers(value = 15, first = 12, count = 2, gas = 2).last()
    assertEquals("1", last.statistics["probesFailed"], "${last.statistics}")
    assertTrue(last.violations.isEmpty(), "${last.messages}")
  }

  @Test
  fun `a reachable condition is sent exactly as without generalization`() {
    val generalized = answers(value = 13, first = 12, count = 2, gas = 2).last()
    val exact = answers(value = 13, first = 12, count = 2, gas = 0).last()
    assertEquals("1", generalized.statistics["probesFailed"], "${generalized.statistics}")
    assertEquals(
      exact.violations.map { it.violationCondition },
      generalized.violations.map { it.violationCondition },
    )
    assertEquals(1, generalized.violations.size)
    assertTrue(!operators.isUnsat(generalized.violations.single().violationCondition!!))
  }

  @Test
  fun `a shape out of gas is no longer probed`() {
    val answers = answers(value = 30, first = 12, count = 4, gas = 1)
    assertEquals("1", answers.last().statistics["probes"], "${answers.last().statistics}")
  }

  @Test
  fun `without gas nothing is probed`() {
    val last = answers(value = 5, first = 12, count = 3, gas = 0).last()
    assertEquals("0", last.statistics["probes"])
    assertTrue(last.violations.isEmpty())
  }
}
