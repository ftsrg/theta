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
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Not
import hu.bme.mit.theta.core.type.inttype.IntExprs.*
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.solver.SolverManager
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.DssPredicateOperators
import hu.bme.mit.theta.xcfa.analysis.dss.decomposition.LinearBlockDecomposition
import hu.bme.mit.theta.xcfa.analysis.dss.ensureDefaultSolversRegistered
import hu.bme.mit.theta.xcfa.cli.params.getDefaultPredCegarConfig
import hu.bme.mit.theta.xcfa.model.*
import java.util.concurrent.LinkedBlockingQueue
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.BeforeAll
import org.junit.jupiter.api.Test

/** The coordinator on the loop `head -(x < n; x++)-> check -(x != -1)-> head`. */
class DssConjectureActorTest {

  companion object {
    @JvmStatic
    @BeforeAll
    fun registerSolvers() {
      ensureDefaultSolversRegistered(getDefaultPredCegarConfig(), NullLogger.getInstance())
    }
  }

  private val operators by lazy { DssPredicateOperators(SolverManager.resolveSolverFactory("Z3")) }

  private val program =
    xcfa("conjectures") {
      val main =
        procedure("main") {
          "x" type Int()
          "n" type Int()
          (init to "head") { "x" assign "0" }
          ("head" to "check") {
            assume("(< x n)")
            "x" assign "(+ x 1)"
          }
          ("check" to err) { assume("(= x (- 0 1))") }
          ("check" to "head") { assume("(/= x (- 0 1))") }
          ("head" to final) { assume("(>= x n)") }
        }
      main.start()
    }

  private val procedure = program.procedures.single()
  private val graph = LinearBlockDecomposition().decompose(procedure)

  @Suppress("UNCHECKED_CAST")
  private fun variable(name: String) =
    (procedure.vars.single { it.name == name } as VarDecl<IntType>).ref

  private val x = variable("x")
  private val n = variable("n")
  private val body =
    graph.blocks.single { it.initialLocation.name == "head" && !it.finalLocation.final }
  private val head = body.initialLocation

  private fun actor(gas: Int = 1, initial: List<Pair<XcfaLocation, *>> = emptyList()) =
    @Suppress("UNCHECKED_CAST")
    DssConjectureActor(
      DssConnection(LinkedBlockingQueue(), DssMessageBroadcaster(emptyMap()), mutableSetOf()),
      graph,
      SolverManager.resolveSolverFactory("Z3"),
      gas,
      initialConjectures =
        initial
          as
          List<
            Pair<
              XcfaLocation,
              hu.bme.mit.theta.core.type.Expr<hu.bme.mit.theta.core.type.booltype.BoolType>,
            >
          >,
    )

  /** The loop head's k-th condition: `x == -2 - k && n >= -1`. */
  private fun condition(k: Int) = And(Eq(x, Int(-2 - k)), Geq(n, Int(-1)))

  private fun DssConjectureActor.receive(k: Int) =
    processMessage(DssViolationConditionMessage(body.id, condition(k))).toList()

  @Test
  fun `drifting conditions at a boundary become a conjecture checked on both sides`() {
    val actor = actor()
    assertTrue(actor.receive(0).isEmpty())
    val conjecture = actor.receive(1).filterIsInstance<DssConjectureMessage>().single()
    assertEquals(
      graph.blocks.filter { it.initialLocation == head }.map { it.id }.toSet(),
      conjecture.restrictedIds,
    )
    assertEquals(
      graph.blocks.filter { it.finalLocation == head }.map { it.id }.toSet(),
      conjecture.obligedIds,
    )
    for (k in 0..1) assertTrue(operators.isLeq(condition(k), conjecture.condition))
    assertTrue(!operators.isUnsat(Not(conjecture.condition)), "${conjecture.condition}")
    assertTrue(conjecture.maxHops > 0 && !conjecture.retracted)
  }

  @Test
  fun `a failed conjecture is retracted everywhere and costs its location gas`() {
    val actor = actor(gas = 1)
    actor.receive(0)
    val conjecture = actor.receive(1).filterIsInstance<DssConjectureMessage>().single()
    val retraction =
      actor.processMessage(DssConjectureFailedMessage(body.id, conjecture.conjecture))
    assertEquals(listOf(true), retraction.map { (it as DssConjectureMessage).retracted })
    assertTrue(
      actor.processMessage(DssConjectureFailedMessage(body.id, conjecture.conjecture)).isEmpty()
    )
    assertTrue((2..4).flatMap { actor.receive(it) }.isEmpty(), "the location is out of gas")
    assertEquals(1, actor.proposed)
    assertEquals(1, actor.retracted)
  }

  @Test
  fun `the program entry is never conjectured`() {
    val actor = actor(initial = listOf(procedure.initLoc to True(), head to True()))
    val proposed = actor.receive(0).filterIsInstance<DssConjectureMessage>()
    assertEquals(
      listOf(graph.blocks.filter { it.initialLocation == head }.map { it.id }.toSet()),
      proposed.map { it.restrictedIds },
    )
  }
}
