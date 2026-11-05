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
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Or
import hu.bme.mit.theta.core.type.inttype.IntExprs.*
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.solver.SolverManager
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.DssAuxVars
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.reverseBlockGraph
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.reverseProgram
import hu.bme.mit.theta.xcfa.analysis.dss.decomposition.Block
import hu.bme.mit.theta.xcfa.analysis.dss.decomposition.BlockGraph
import hu.bme.mit.theta.xcfa.analysis.dss.ensureDefaultSolversRegistered
import hu.bme.mit.theta.xcfa.cli.params.getDefaultPredCegarConfig
import hu.bme.mit.theta.xcfa.model.*
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertNotNull
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.BeforeAll
import org.junit.jupiter.api.Test

/** The meeting actor's verdicts and exchanges, fed by hand-made messages. */
class DssMeetingActorTest {

  companion object {

    @JvmStatic
    @BeforeAll
    fun registerSolvers() {
      ensureDefaultSolversRegistered(getDefaultPredCegarConfig(), NullLogger.getInstance())
    }
  }

  /** `init -A-> l1 -B-> l2 -C-> err`, cut by hand so that `l1` and `l2` are block boundaries. */
  private val xcfa =
    xcfa("meet") {
      val main =
        procedure("main") {
          "x" type Int()
          "y" type Int()
          (init to "l1") { "x" assign "0" }
          ("l1" to "l2") { "x" assign "(+ x 1)" }
          ("l2" to err) { assume("(= x 1)") }
        }
      main.start()
    }
  private val procedure = xcfa.procedures.single()

  @Suppress("UNCHECKED_CAST")
  private fun intVar(name: String) = procedure.vars.single { it.name == name } as VarDecl<IntType>

  private val x = intVar("x").ref
  private val y = intVar("y").ref

  private fun location(name: String) = procedure.locs.single { it.name == name }

  private fun block(id: String, from: XcfaLocation, to: XcfaLocation) =
    Block(id, from, to, setOf(from, to), from.outgoingEdges.filter { it.target == to }.toSet())

  private val forward =
    BlockGraph.fromBlocksWithoutEdges(
      listOf(
        block("A", procedure.initLoc, location("l1")),
        block("B", location("l1"), location("l2")),
        block("C", location("l2"), procedure.errorLoc.get()),
      )
    )
  private val reversal = reverseProgram(xcfa)
  private val backward = reverseBlockGraph(forward, reversal).withIdPrefix("R.")

  private fun actor(shareInvariants: Boolean = true) =
    DssMeetingActor(
      DssConnection(createDssMessageQueue(), DssMessageBroadcaster(emptyMap()), mutableSetOf()),
      procedure,
      DssMeetingSide(forward, procedure.locs.associateWith { it }),
      DssMeetingSide(backward, reversal.originalOf),
      SolverManager.resolveSolverFactory("Z3"),
      sharedVars = setOf(intVar("x")),
      shareInvariants = shareInvariants,
    )

  private fun post(
    id: String,
    state: Expr<BoolType>,
    version: Int,
    vararg inputs: Pair<String, Int>,
  ) = DssPostConditionMessage(id, listOf(state), version = version, inputs = inputs.toMap())

  /** A converged backward network: `x == 1` reaches the error at `l2`, `x == 0` at `l1`. */
  private val backwardChain =
    listOf(
      post("R.init", True(), 1),
      post("R.error0", True(), 1, "R.init" to 1),
      post("R.C", Eq(x, Int(1)), 1, "R.error0" to 1),
      post("R.B", Eq(x, Int(0)), 1, "R.C" to 1),
    )

  private fun DssMeetingActor.feed(messages: List<DssMessage>): List<DssMessage> =
    messages.flatMap { processMessage(it) }

  private fun List<DssMessage>.verdicts() = filterIsInstance<DssResultMessage>().map { it.result }

  @Test
  fun `the reversed blocks share the forward boundaries`() {
    val ids = backward.blocks.map { it.id }.toSet()
    assertEquals(setOf("R.init", "R.error0", "R.entry", "R.A", "R.B", "R.C"), ids)
  }

  @Test
  fun `disjoint certified summaries on a cut prove SAFE`() {
    val actor = actor()
    actor.feed(backwardChain)
    val answer =
      actor.feed(listOf(post("A", Eq(x, Int(0)), 1), post("B", Eq(x, Int(6)), 1, "A" to 1)))
    assertEquals(listOf(DssResult.SAFE), answer.verdicts())
  }

  /** Before a fixpoint, a postcondition may miss reachable states: it must not cut any path. */
  @Test
  fun `a postcondition computed from an outdated input is not certified`() {
    val actor = actor()
    actor.feed(backwardChain)
    val early =
      actor.feed(
        listOf(
          post("A", Eq(x, Int(5)), 1),
          post("A", Eq(x, Int(0)), 2),
          post("B", Eq(x, Int(6)), 1, "A" to 1),
        )
      )
    assertTrue(early.verdicts().isEmpty()) { "$early" }
    val converged = actor.feed(listOf(post("B", Eq(x, Int(6)), 2, "A" to 2)))
    assertEquals(listOf(DssResult.SAFE), converged.verdicts())
  }

  @Test
  fun `an input covering the newest postcondition counts as converged`() {
    val actor = actor()
    actor.feed(backwardChain)
    val answer =
      actor.feed(
        listOf(
          post("A", Or(Eq(x, Int(0)), Eq(x, Int(5))), 1),
          post("A", Eq(x, Int(0)), 2),
          post("B", Eq(x, Int(6)), 1, "A" to 1),
        )
      )
    assertEquals(listOf(DssResult.SAFE), answer.verdicts())
  }

  @Test
  fun `a postcondition without all its inputs is not certified`() {
    val actor = actor()
    actor.feed(backwardChain)
    val answer = actor.feed(listOf(post("A", Eq(x, Int(0)), 1), post("B", Eq(x, Int(6)), 1)))
    assertTrue(answer.verdicts().isEmpty()) { "$answer" }
  }

  @Test
  fun `exact conditions meet with their auxiliary variables kept apart`() {
    val actor = actor()
    val aux = DssAuxVars.of(0, Int()).ref as Expr<IntType>
    val forwardCondition = And(Eq(x, aux), Gt(aux, Int(5)))
    val backwardCondition = Eq(x, Add(aux, Int(10)))
    val answer =
      actor.feed(
        listOf(
          DssViolationConditionMessage("C", forwardCondition),
          DssViolationConditionMessage("R.B", backwardCondition),
        )
      )
    assertEquals(listOf(DssResult.UNSAFE), answer.verdicts())
    val meet = actor.meet
    assertNotNull(meet)
    assertEquals("C" to "R.B", meet!!.forwardBlock to meet.backwardBlock)
  }

  @Test
  fun `disjoint exact conditions do not meet`() {
    val actor = actor()
    val answer =
      actor.feed(
        listOf(
          DssViolationConditionMessage("C", Eq(x, Int(3))),
          DssViolationConditionMessage("R.B", Eq(x, Int(4))),
        )
      )
    assertTrue(answer.isEmpty()) { "$answer" }
  }

  @Test
  fun `certified summaries go to the other direction once, over shared variables only`() {
    val actor = actor()
    val backwardAnswer = actor.feed(backwardChain).filterIsInstance<DssRestrictionMessage>()
    // l2 and l1 are certified backward: forward C and B start there
    assertEquals(
      setOf(setOf("C") to Eq(x, Int(1)), setOf("B") to Eq(x, Int(0))),
      backwardAnswer.map { it.targetIds to it.restriction }.toSet(),
    )
    val first = actor.feed(listOf(post("A", Eq(x, Int(0)), 1)))
    assertEquals(
      listOf(setOf("R.A") to Eq(x, Int(0))),
      first.filterIsInstance<DssRestrictionMessage>().map { it.targetIds to it.restriction },
    )
    val repeated = actor.feed(listOf(post("A", Eq(x, Int(0)), 2)))
    assertTrue(repeated.isEmpty()) { "$repeated" }
    val unshared = actor.feed(listOf(post("A", Eq(y, Int(0)), 3)))
    assertTrue(unshared.none { it is DssRestrictionMessage }) { "$unshared" }
  }

  @Test
  fun `without sharing, nothing is sent`() {
    val actor = actor(shareInvariants = false)
    assertTrue(actor.feed(backwardChain + post("A", Eq(x, Int(0)), 1)).isEmpty())
  }
}
