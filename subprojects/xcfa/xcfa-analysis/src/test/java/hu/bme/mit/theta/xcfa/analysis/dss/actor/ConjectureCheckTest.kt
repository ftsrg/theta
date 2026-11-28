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
import hu.bme.mit.theta.core.type.booltype.BoolExprs.False
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And
import hu.bme.mit.theta.core.type.inttype.IntExprs.*
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.solver.SolverManager
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.DssCheckerRoster
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.DssPredicateOperators
import hu.bme.mit.theta.xcfa.analysis.dss.decomposition.Block
import hu.bme.mit.theta.xcfa.analysis.dss.decomposition.BlockGraph
import hu.bme.mit.theta.xcfa.analysis.dss.decomposition.LinearBlockDecomposition
import hu.bme.mit.theta.xcfa.analysis.dss.ensureDefaultSolversRegistered
import hu.bme.mit.theta.xcfa.cli.checkers.getCegarChecker
import hu.bme.mit.theta.xcfa.cli.params.getDefaultPredCegarConfig
import hu.bme.mit.theta.xcfa.model.*
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.BeforeAll
import org.junit.jupiter.api.Test

/** How blocks check conjectures, on `init -(x := 6)-> a -(x := x + 1)-> b`, then an error. */
class ConjectureCheckTest {

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

  private val program =
    xcfa("conjecture") {
      val main =
        procedure("main") {
          "x" type Int()
          (init to "a") { "x" assign "6" }
          ("a" to "b") { "x" assign "(+ x 1)" }
          ("b" to final) { assume("(< x 10)") }
          ("b" to err) { assume("(>= x 10)") }
        }
      main.start()
    }

  private val procedure = program.procedures.single()
  // A straight line is one linear block; the step from a to b gets its own
  private val graph: BlockGraph =
    LinearBlockDecomposition { it.name == "a" || LinearBlockDecomposition.defaultIsBlockEnd(it) }
      .decompose(procedure)

  @Suppress("UNCHECKED_CAST")
  private val x = (procedure.vars.single { it.name == "x" } as VarDecl<IntType>).ref

  private val step: Block = graph.blocks.single { it.initialLocation.name == "a" }

  private fun behavior(block: Block) = PredicateBlockBehavior(program, procedure, block, roster)

  /** [step] after its predecessor's postcondition `x == 6`. */
  private fun stepWithPrecondition(): PredicateBlockBehavior =
    behavior(step).also {
      it.runInitialAnalysis()
      it.onPostCondition(DssPostConditionMessage(graph.root.id, Eq(x, Int(6))))
    }

  private fun obligation(block: Block, condition: hu.bme.mit.theta.core.type.Expr<*>, hops: Int) =
    @Suppress("UNCHECKED_CAST")
    DssConjectureMessage(
      COORDINATOR_ID,
      0,
      condition as hu.bme.mit.theta.core.type.Expr<hu.bme.mit.theta.core.type.booltype.BoolType>,
      obligedIds = setOf(block.id),
      maxHops = hops,
    )

  @Test
  fun `the root reaching a conjectured condition refutes the conjecture, never the program`() {
    val root = behavior(graph.root).also { it.runInitialAnalysis() }
    val messages = root.onConjecture(obligation(graph.root, Eq(x, Int(6)), hops = 4))
    assertEquals(listOf(DssConjectureFailedMessage(graph.root.id, 0)), messages.toList())
  }

  @Test
  fun `a condition no start state reaches is refuted silently`() {
    val root = behavior(graph.root).also { it.runInitialAnalysis() }
    assertTrue(root.onConjecture(obligation(graph.root, Eq(x, Int(7)), hops = 4)).isEmpty())
    val successor = graph.blocks.single { it.initialLocation.name == "b" && it.finalLocation.error }
    val far = DssMayViolationMessage(successor.id, 0, Geq(x, Int(8)), hopsLeft = 3)
    assertTrue(root.onMayViolation(far).isEmpty())
  }

  @Test
  fun `a reached condition goes back as its weakest precondition with one hop less`() {
    val messages = stepWithPrecondition().onConjecture(obligation(step, Geq(x, Int(7)), hops = 4))
    val sent = messages.filterIsInstance<DssMayViolationMessage>().single()
    assertEquals(3, sent.hopsLeft)
    assertTrue(messages.none { it is DssViolationConditionMessage }, "$messages")
    // x + 1 >= 7, i.e. x >= 6
    assertTrue(operators.isLeq(sent.condition, Geq(x, Int(6))), "${sent.condition}")
    assertTrue(operators.isLeq(Geq(x, Int(6)), sent.condition), "${sent.condition}")
  }

  @Test
  fun `a chain out of hops refutes the conjecture`() {
    val messages = stepWithPrecondition().onConjecture(obligation(step, Geq(x, Int(7)), hops = 0))
    assertEquals(listOf(DssConjectureFailedMessage(step.id, 0)), messages.toList())
  }

  @Test
  fun `a retracted conjecture ignores its late may violations`() {
    val block = stepWithPrecondition()
    block.onConjecture(obligation(step, Geq(x, Int(100)), hops = 4))
    val retraction = DssConjectureMessage(COORDINATOR_ID, 0, False(), retracted = true)
    assertTrue(block.onConjecture(retraction).isEmpty())
    val successor = graph.blocks.single { it.initialLocation.name == "b" && it.finalLocation.error }
    val late = DssMayViolationMessage(successor.id, 0, Geq(x, Int(7)), hopsLeft = 3)
    assertTrue(block.onMayViolation(late).isEmpty())
  }

  @Test
  fun `an assumed conjecture restricts the start states until it is retracted`() {
    val block = stepWithPrecondition()
    val assumed =
      DssConjectureMessage(COORDINATOR_ID, 0, Eq(x, Int(6)), restrictedIds = setOf(step.id))
    // No start state is left, so no exit state: nothing is sent, successors keep the older one
    val excluded = block.onConjecture(assumed).filterIsInstance<DssPostConditionMessage>()
    assertTrue(excluded.isEmpty(), "$excluded")
    val retraction = DssConjectureMessage(COORDINATOR_ID, 0, Eq(x, Int(6)), retracted = true)
    val post = block.onConjecture(retraction).filterIsInstance<DssPostConditionMessage>().single()
    assertTrue(!post.restricted)
    assertTrue(!operators.isUnsat(And(post.postcondition!!, Eq(x, Int(7)))), "$post")
    val other =
      DssConjectureMessage(COORDINATOR_ID, 1, Eq(x, Int(5)), restrictedIds = setOf(step.id))
    val kept = block.onConjecture(other).filterIsInstance<DssPostConditionMessage>().single()
    assertTrue(kept.restricted, "$kept")
    assertTrue(!operators.isUnsat(And(kept.postcondition!!, Eq(x, Int(7)))), "$kept")
  }
}
