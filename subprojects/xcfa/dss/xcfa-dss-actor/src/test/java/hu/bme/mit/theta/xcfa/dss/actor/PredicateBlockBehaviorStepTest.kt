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
package hu.bme.mit.theta.xcfa.dss.actor

import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.False
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And
import hu.bme.mit.theta.core.type.inttype.IntExprs.*
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.solver.SolverManager
import hu.bme.mit.theta.xcfa.cli.checkers.getCegarChecker
import hu.bme.mit.theta.xcfa.cli.params.getDefaultPredCegarConfig
import hu.bme.mit.theta.xcfa.cli.utils.ensureDefaultSolversRegistered
import hu.bme.mit.theta.xcfa.dss.analysis.DssCheckerRoster
import hu.bme.mit.theta.xcfa.dss.analysis.DssPredicateOperators
import hu.bme.mit.theta.xcfa.dss.decomposition.Block
import hu.bme.mit.theta.xcfa.dss.decomposition.BlockGraph
import hu.bme.mit.theta.xcfa.dss.decomposition.LinearBlockDecomposition
import hu.bme.mit.theta.xcfa.model.*
import org.junit.jupiter.api.Assertions.assertFalse
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.BeforeAll
import org.junit.jupiter.api.Test

/**
 * Drives [PredicateBlockBehavior]'s individual steps (CPAchecker's `DssBlockAnalysis` methods)
 * directly, without the actor runtime, and checks the messages each step produces.
 */
class PredicateBlockBehaviorStepTest {

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

  private fun equivalent(a: Expr<BoolType>, b: Expr<BoolType>) =
    operators.isLeq(a, b) && operators.isLeq(b, a)

  @Suppress("UNCHECKED_CAST")
  private fun XCFA.intVar(name: String) =
    procedures.single().vars.single { it.name == name } as VarDecl<IntType>

  /** init -(x := value)-> branch; branch -(x < 10)-> safe -> final; branch -(x >= 10)-> err. */
  private fun branching(value: String): XCFA =
    xcfa("steps") {
      val main =
        procedure("main") {
          "x" type Int()
          (init to "branch") { "x" assign value }
          ("branch" to "safe") { assume("(< x 10)") }
          ("branch" to "unsafe") { assume("(>= x 10)") }
          ("safe" to final) { nop() }
          ("unsafe" to err) { nop() }
        }
      main.start()
    }

  /**
   * init -(havoc x)-> a; a -> j and a -> b -> j (a join); j -(x := x + 1)-> k; k -(x > 5)-> err.
   * With every location a block boundary, the block `j -> k` has two predecessors.
   */
  private fun join(): XCFA =
    xcfa("vc-before-pre") {
      val main =
        procedure("main") {
          "x" type Int()
          (init to "a") { havoc("x") }
          ("a" to "j") { nop() }
          ("a" to "b") { nop() }
          ("b" to "j") { nop() }
          ("j" to "k") { "x" assign "(+ x 1)" }
          ("k" to err) { assume("(> x 5)") }
        }
      main.start()
    }

  private class Fixture(val program: XCFA, val graph: BlockGraph) {
    val procedure: XcfaProcedure = program.procedures.single()

    fun block(predicate: (Block) -> Boolean) = graph.blocks.single(predicate)

    fun errorBlock() = block { b -> b.locations.any { it.error } }
  }

  private fun linear(program: XCFA) =
    Fixture(program, LinearBlockDecomposition().decompose(program.procedures.single()))

  private fun everyLocationABoundary(program: XCFA) =
    Fixture(
      program,
      LinearBlockDecomposition(isBlockEnd = { true }).decompose(program.procedures.single()),
    )

  private fun Fixture.behavior(block: Block) =
    PredicateBlockBehavior(program, procedure, block, roster)

  @Test
  fun `the initial analysis of a block with an error sends its path condition, and no postcondition without successors`() {
    val f = linear(branching("5"))
    val x = f.program.intVar("x").ref

    val messages = f.behavior(f.errorBlock()).runInitialAnalysis()

    val vc = messages.filterIsInstance<DssViolationConditionMessage>().single().violationCondition!!
    assertTrue(equivalent(vc, Geq(x, Int(10))), "$vc")
    assertTrue(messages.none { it is DssPostConditionMessage }, "$messages")
  }

  @Test
  fun `the initial analysis of a safe block sends its postcondition`() {
    val f = linear(branching("5"))
    val x = f.program.intVar("x").ref

    val messages = f.behavior(f.graph.root).runInitialAnalysis()

    val post = messages.filterIsInstance<DssPostConditionMessage>().single().postcondition!!
    assertTrue(operators.isLeq(post, Lt(x, Int(10))), "$post")
    assertTrue(messages.none { it is DssViolationConditionMessage })
  }

  @Test
  fun `the root refutes an unreachable violation condition and answers with a postcondition`() {
    val f = linear(branching("5"))
    val x = f.program.intVar("x").ref
    val root = f.behavior(f.graph.root)
    root.runInitialAnalysis()

    val answer =
      root.onViolationCondition(DssViolationConditionMessage(f.errorBlock().id, Geq(x, Int(10))))

    assertTrue(answer.none { it is DssViolationConditionMessage }, "$answer")
    assertTrue(answer.any { it is DssPostConditionMessage }, "$answer")
  }

  @Test
  fun `the root reports a reachable violation condition, which means UNSAFE`() {
    val f = linear(branching("20"))
    val x = f.program.intVar("x").ref
    val root = f.behavior(f.graph.root)
    root.runInitialAnalysis()

    val answer =
      root.onViolationCondition(DssViolationConditionMessage(f.errorBlock().id, Geq(x, Int(10))))

    val vc = answer.filterIsInstance<DssViolationConditionMessage>().single().violationCondition!!
    assertFalse(operators.isUnsat(vc))
  }

  @Test
  fun `preconditions are covered per sender - stronger ones replace, weaker ones are ignored`() {
    val f = linear(branching("5"))
    val x = f.program.intVar("x").ref
    val behavior = f.behavior(f.errorBlock())
    val sender = f.graph.root.id

    assertTrue(behavior.storePrecondition(DssPostConditionMessage(sender, Lt(x, Int(10)))))
    assertTrue(behavior.storePrecondition(DssPostConditionMessage(sender, Lt(x, Int(5)))))
    assertFalse(
      behavior.storePrecondition(DssPostConditionMessage(sender, Lt(x, Int(20)))),
      "a state implied by a stored state of the same sender is not relevant",
    )
    assertFalse(behavior.storePrecondition(DssPostConditionMessage(sender, Lt(x, Int(5)))))
  }

  @Test
  fun `violation conditions are stored unless unsatisfiable or repeated`() {
    val f = linear(branching("5"))
    val x = f.program.intVar("x").ref
    val behavior = f.behavior(f.graph.root)
    val sender = f.errorBlock().id

    assertFalse(behavior.storeViolationCondition(DssViolationConditionMessage(sender, False())))
    assertFalse(
      behavior.storeViolationCondition(
        DssViolationConditionMessage(sender, And(Lt(x, Int(0)), Gt(x, Int(0))))
      )
    )
    assertTrue(
      behavior.storeViolationCondition(DssViolationConditionMessage(sender, Gt(x, Int(1))))
    )
    assertFalse(
      behavior.storeViolationCondition(DssViolationConditionMessage(sender, Gt(x, Int(1))))
    )
    assertTrue(
      behavior.storeViolationCondition(DssViolationConditionMessage(sender, Gt(x, Int(2))))
    )
  }

  @Test
  fun `a block without violations does not re-analyze new preconditions, like CPAchecker's`() {
    val f = linear(branching("5"))
    val x = f.program.intVar("x").ref
    val safeBlock = f.block { b -> b.locations.any { it.final } }
    val behavior = f.behavior(safeBlock)
    behavior.runInitialAnalysis()

    assertTrue(
      behavior.onPostCondition(DssPostConditionMessage(f.graph.root.id, Lt(x, Int(3)))).isEmpty()
    )
  }

  /**
   * Regression test (wrong SAFE): CPAchecker assumes an early violation condition is re-sent later
   * ("the same vc must have been sent already"); Theta checks that instead.
   */
  @Test
  fun `a violation condition that arrives before any precondition is still propagated`() {
    val f = everyLocationABoundary(join())
    val x = f.program.intVar("x").ref
    val increment = f.block { it.initialLocation.name == "j" }
    val behavior = f.behavior(increment)
    behavior.runInitialAnalysis()

    assertTrue(
      behavior
        .onViolationCondition(DssViolationConditionMessage(f.errorBlock().id, Gt(x, Int(5))))
        .isEmpty(),
      "nothing to analyze yet - no precondition",
    )
    // The other predecessor has not reported yet, so top is analyzed besides this state.
    val answer =
      behavior.onPostCondition(
        DssPostConditionMessage(
          increment.predecessorIds.first(),
          listOf(True()),
          setOf(Gt(x, Int(0))),
        )
      )

    val vc = answer.filterIsInstance<DssViolationConditionMessage>().single().violationCondition!!
    assertTrue(equivalent(vc, Gt(x, Int(4))), "$vc")
  }

  @Test
  fun `a non-root block propagates the weakest precondition of a reachable violation condition`() {
    val f = everyLocationABoundary(join())
    val x = f.program.intVar("x").ref
    val increment = f.block { it.initialLocation.name == "j" }
    val behavior = f.behavior(increment)
    behavior.runInitialAnalysis()
    for (predecessor in increment.predecessorIds) {
      behavior.onPostCondition(DssPostConditionMessage(predecessor, True()))
    }

    val answer =
      behavior.onViolationCondition(DssViolationConditionMessage(f.errorBlock().id, Gt(x, Int(5))))

    val vc = answer.filterIsInstance<DssViolationConditionMessage>().single().violationCondition!!
    assertTrue(equivalent(vc, Gt(x, Int(4))), "$vc")
  }

  @Test
  fun `a refuted violation condition is not propagated and refines the postcondition`() {
    val f = everyLocationABoundary(join())
    val x = f.program.intVar("x").ref
    val increment = f.block { it.initialLocation.name == "j" }
    val behavior = f.behavior(increment)
    behavior.runInitialAnalysis()
    for (predecessor in increment.predecessorIds) {
      behavior.onPostCondition(DssPostConditionMessage(predecessor, Lt(x, Int(3))))
    }

    val answer =
      behavior.onViolationCondition(DssViolationConditionMessage(f.errorBlock().id, Gt(x, Int(5))))

    assertTrue(answer.none { it is DssViolationConditionMessage }, "$answer")
    val post = answer.filterIsInstance<DssPostConditionMessage>().single().postcondition!!
    assertTrue(operators.isUnsat(And(post, Gt(x, Int(5)))), "$post")
  }
}
