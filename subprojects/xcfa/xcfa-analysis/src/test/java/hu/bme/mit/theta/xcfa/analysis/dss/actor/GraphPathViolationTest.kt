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
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.DssOriginPostcondition
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.DssPreconditionHandling
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.DssPredicateOperators
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.DssViolationConditions
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.DssViolationMessages
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.DssViolationStorage
import hu.bme.mit.theta.xcfa.analysis.dss.decomposition.SingleBlockDecomposition
import hu.bme.mit.theta.xcfa.analysis.dss.ensureDefaultSolversRegistered
import hu.bme.mit.theta.xcfa.cli.checkers.getCegarChecker
import hu.bme.mit.theta.xcfa.cli.params.Refinement
import hu.bme.mit.theta.xcfa.cli.params.getDefaultPredCegarConfig
import hu.bme.mit.theta.xcfa.model.*
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertFalse
import org.junit.jupiter.api.Assertions.assertThrows
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

  private fun behavior(
    program: XCFA,
    mode: DssViolationConditions,
    refinement: Refinement = Refinement.MULTI_SEQ,
    keepProofTree: Boolean = true,
    knownPathSearch: Boolean = true,
    violationMessages: DssViolationMessages = DssViolationMessages.DISJUNCTION,
    violationStorage: DssViolationStorage = DssViolationStorage.SENDER,
  ): PredicateBlockBehavior {
    val procedure = program.procedures.single()
    val block = SingleBlockDecomposition.decompose(procedure).root
    return PredicateBlockBehavior(
      program,
      procedure,
      block,
      roster(refinement, keepProofTree),
      // The program's assumptions as predicates would refute the spurious path abstractly
      useGlobalPredicatePool = false,
      violationConditionMode = mode,
      knownPathSearch = knownPathSearch,
      violationMessages = violationMessages,
      violationStorage = violationStorage,
    )
  }

  private fun initialAnalysis(
    program: XCFA,
    mode: DssViolationConditions,
    refinement: Refinement = Refinement.MULTI_SEQ,
    keepProofTree: Boolean = true,
  ): Pair<Expr<BoolType>, Map<String, String>> {
    val behavior = behavior(program, mode, refinement, keepProofTree)
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
  fun `a run that finds only the known path looks for the other one`() {
    val x = twoErrors.intVar("x").ref
    val both = Or(Gt(x, Int(5)), Lt(x, Int(-5)))
    val behavior = behavior(twoErrors, DssViolationConditions.PATHS, Refinement.SEQ_ITP)
    behavior.runInitialAnalysis()

    val again = behavior.analyzePrecondition()

    val vc = again.filterIsInstance<DssViolationConditionMessage>().single().violationCondition!!
    assertTrue(equivalent(vc, both), "after the search: $vc")
  }

  @Test
  fun `without the known path search, a run that finds only the known path sends nothing`() {
    val behavior =
      behavior(twoErrors, DssViolationConditions.PATHS, Refinement.SEQ_ITP, knownPathSearch = false)
    behavior.runInitialAnalysis()

    val again = behavior.analyzePrecondition()

    assertTrue(again.none { it is DssViolationConditionMessage }, "$again")
    // The initial run, then the run that finds the known path and the one without targets for the
    // postcondition: no search run
    assertEquals("3", behavior.statistics()["analyses"], "${behavior.statistics()}")
  }

  @Test
  fun `with per-path messages, each error path is sent on its own`() {
    val x = twoErrors.intVar("x").ref
    val behavior =
      behavior(
        twoErrors,
        DssViolationConditions.GRAPH_PATHS,
        violationMessages = DssViolationMessages.PER_PATH,
      )

    val messages = behavior.runInitialAnalysis().filterIsInstance<DssViolationConditionMessage>()

    assertEquals(2, messages.size, "$messages")
    assertTrue(messages.all { it.addsPath }, "$messages")
    val conditions = messages.map { it.violationCondition!! }
    assertTrue(conditions.any { equivalent(it, Gt(x, Int(5))) }, "$conditions")
    assertTrue(conditions.any { equivalent(it, Lt(x, Int(-5))) }, "$conditions")
  }

  @Test
  fun `a per-path message adds to the sender's earlier paths`() {
    val x = twoErrors.intVar("x").ref
    val receiver = behavior(twoErrors, DssViolationConditions.PATHS)
    val high = DssViolationConditionMessage("succ", Gt(x, Int(5)), addsPath = true)
    val low = DssViolationConditionMessage("succ", Lt(x, Int(-5)), addsPath = true)

    assertTrue(receiver.storeViolationCondition(high))
    assertTrue(receiver.storeViolationCondition(low))
    assertFalse(receiver.storeViolationCondition(high), "a known path is no news")
    // A message without the flag replaces both, so the other path is news again
    assertFalse(
      receiver.storeViolationCondition(DssViolationConditionMessage("succ", Gt(x, Int(5))))
    )
    assertTrue(receiver.storeViolationCondition(low))
  }

  @Test
  fun `with storage by origin, each path is sent with the edges it takes`() {
    val behavior =
      behavior(
        twoErrors,
        DssViolationConditions.GRAPH_PATHS,
        violationMessages = DssViolationMessages.PER_PATH,
        violationStorage = DssViolationStorage.ORIGIN,
      )

    val messages = behavior.runInitialAnalysis().filterIsInstance<DssViolationConditionMessage>()

    assertEquals(2, messages.size, "$messages")
    assertTrue(messages.all { it.origin.isNotEmpty() }, "$messages")
    assertEquals(2, messages.map { it.origin }.toSet().size, "$messages")
  }

  @Test
  fun `with storage by origin, a condition whose path includes a kept one's is not kept`() {
    val x = twoErrors.intVar("x").ref
    val receiver =
      behavior(
        twoErrors,
        DssViolationConditions.PATHS,
        Refinement.SEQ_ITP,
        violationMessages = DssViolationMessages.PER_PATH,
        violationStorage = DssViolationStorage.ORIGIN,
      )
    fun path(condition: Expr<BoolType>, vararg edges: String) =
      DssViolationConditionMessage("succ", condition, addsPath = true, origin = edges.toSet())

    receiver.onViolationCondition(path(Gt(x, Int(5)), "a->b"))
    receiver.onViolationCondition(path(Gt(x, Int(6)), "a->b", "b->c"))
    receiver.onViolationCondition(path(Lt(x, Int(-5)), "a->d"))
    receiver.onViolationCondition(path(Lt(x, Int(-5)), "a->d"))

    val stats = receiver.statistics()
    assertEquals("4", stats["vcReceived"], "$stats")
    assertEquals("2", stats["vcKept"], "$stats")
  }

  @Test
  fun `the postcondition without received conditions needs reset precisions`() {
    assertThrows(IllegalArgumentException::class.java) {
      PredicateBlockBehavior(
        twoErrors,
        twoErrors.procedures.single(),
        SingleBlockDecomposition.decompose(twoErrors.procedures.single()).root,
        roster(Refinement.MULTI_SEQ, true),
        violationConditionMode = DssViolationConditions.PATHS,
        violationMessages = DssViolationMessages.PER_PATH,
        violationStorage = DssViolationStorage.ORIGIN,
        originPostcondition = DssOriginPostcondition.NO_CONDITIONS,
      )
    }
  }

  @Test
  fun `with CPAchecker's precondition handling, a postcondition implying the stored one is no news`() {
    val x = twoErrors.intVar("x").ref
    val procedure = twoErrors.procedures.single()
    val block =
      SingleBlockDecomposition.decompose(procedure).root.copy(predecessorIds = setOf("pred"))
    val behavior =
      PredicateBlockBehavior(
        twoErrors,
        procedure,
        block,
        roster(Refinement.SEQ_ITP, false),
        useGlobalPredicatePool = false,
        violationConditionMode = DssViolationConditions.PATHS,
        violationMessages = DssViolationMessages.PER_PATH,
        violationStorage = DssViolationStorage.ORIGIN,
        preconditionHandling = DssPreconditionHandling.CPACHECKER,
      )
    fun analyses() = behavior.statistics().getValue("analyses").toInt()
    behavior.onViolationCondition(
      DssViolationConditionMessage("succ", Gt(x, Int(100)), addsPath = true, origin = setOf("e"))
    )

    val beforeFirst = analyses()
    behavior.onPostCondition(DssPostConditionMessage("pred", Gt(x, Int(0))))
    val afterFirst = analyses()
    behavior.onPostCondition(DssPostConditionMessage("pred", Gt(x, Int(3))))
    val afterStronger = analyses()
    behavior.onPostCondition(DssPostConditionMessage("pred", Gt(x, Int(-1))))
    val afterWeaker = analyses()

    assertTrue(afterFirst > beforeFirst, "the first postcondition reruns the kept condition")
    assertEquals(afterFirst, afterStronger, "a stronger postcondition reruns nothing")
    assertTrue(afterWeaker > afterStronger, "a weaker postcondition reruns")
  }

  @Test
  fun `CPAchecker's precondition handling and the rerun from top need storage by origin`() {
    for ((handling, fromTop) in
      listOf(DssPreconditionHandling.CPACHECKER to false, DssPreconditionHandling.THETA to true)) {
      assertThrows(IllegalArgumentException::class.java) {
        PredicateBlockBehavior(
          twoErrors,
          twoErrors.procedures.single(),
          SingleBlockDecomposition.decompose(twoErrors.procedures.single()).root,
          roster(Refinement.MULTI_SEQ, true),
          preconditionHandling = handling,
          newOriginFromTop = fromTop,
        )
      }
    }
  }

  @Test
  fun `storage by origin needs per-path messages`() {
    assertThrows(IllegalArgumentException::class.java) {
      behavior(
        twoErrors,
        DssViolationConditions.PATHS,
        violationStorage = DssViolationStorage.ORIGIN,
      )
    }
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
