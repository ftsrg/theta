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
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Or
import hu.bme.mit.theta.core.type.inttype.IntExprs.*
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.solver.SolverManager
import hu.bme.mit.theta.xcfa.analysis.dss.actor.DssBlockWitness
import hu.bme.mit.theta.xcfa.analysis.dss.actor.backwardInvariants
import hu.bme.mit.theta.xcfa.analysis.dss.actor.combineInvariants
import hu.bme.mit.theta.xcfa.analysis.dss.decomposition.Block
import hu.bme.mit.theta.xcfa.analysis.dss.decomposition.BlockGraph
import hu.bme.mit.theta.xcfa.analysis.dss.ensureDefaultSolversRegistered
import hu.bme.mit.theta.xcfa.cli.params.getDefaultPredCegarConfig
import hu.bme.mit.theta.xcfa.model.*
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertFalse
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.BeforeAll
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.assertThrows

class ProgramReversalTest {

  companion object {

    @JvmStatic
    @BeforeAll
    fun registerSolvers() {
      ensureDefaultSolversRegistered(getDefaultPredCegarConfig(), NullLogger.getInstance())
    }
  }

  private val operators by lazy { DssPredicateOperators(SolverManager.resolveSolverFactory("Z3")) }

  private fun assertEquivalent(expected: Expr<BoolType>, actual: Expr<BoolType>) {
    assertTrue(operators.isLeq(expected, actual) && operators.isLeq(actual, expected)) {
      "expected $expected, got $actual"
    }
  }

  @Suppress("UNCHECKED_CAST")
  private fun XcfaProcedure.intVar(name: String) =
    vars.single { it.name == name } as VarDecl<IntType>

  /** The exact states at the original error that the original entry reaches, via [reversal]. */
  private fun reachableAtError(reversal: ProgramReversal): Expr<BoolType> {
    val procedure = reversal.procedure
    val error = procedure.errorLoc.get()
    val block = Block("R", procedure.initLoc, error, procedure.locs, procedure.edges)
    return computeViolationCondition(block, mapOf(error to True()))
  }

  private fun counterXcfa(bad: Int): XCFA =
    xcfa("counter") {
      val main =
        procedure("main") {
          "x" type Int()
          "y" type Int()
          (init to "a") { "x" assign "0" }
          ("a" to "b") { "x" assign "(+ x 1)" }
          ("b" to "c") { "y" assign "(* 2 x)" }
          ("c" to "branch") { nop() }
          ("branch" to err) { assume("(= x $bad)") }
          ("branch" to final) { assume("(/= x $bad)") }
        }
      main.start()
    }

  @Test
  fun `the reversed program starts at the errors and ends at the original entry`() {
    val xcfa = counterXcfa(bad = 1)
    val original = xcfa.procedures.single()
    val reversal = reverseProgram(xcfa)
    val procedure = reversal.procedure

    val errorClone = reversal.reversedOf.getValue(original.errorLoc.get())
    val hub = procedure.initLoc.outgoingEdges.single().target
    assertEquals(setOf(errorClone), hub.outgoingEdges.map { it.target }.toSet())
    val entryClone = reversal.reversedOf.getValue(original.initLoc)
    assertEquals(entryClone, procedure.errorLoc.get())
    assertTrue(entryClone.error && entryClone.outgoingEdges.isEmpty())
    assertTrue(procedure.locs.none { it.error && it != procedure.errorLoc.get() })
    // The final location cannot reach the error
    assertTrue(original.finalLoc.get() !in reversal.reversedOf)
    assertTrue(procedure.locs.none { it in original.locs })
  }

  @Test
  fun `an entry that edges enter is followed by a dead-end error`() {
    val xcfa =
      xcfa("reentry") {
        val main =
          procedure("main") {
            "x" type Int()
            (init to "a") { "x" assign "(+ x 1)" }
            ("a" to init) { assume("(< x 5)") }
            ("a" to err) { assume("(= x 5)") }
          }
        main.start()
      }
    val original = xcfa.procedures.single()
    assertTrue(original.initLoc.incomingEdges.isNotEmpty())
    val reversal = reverseProgram(xcfa)
    val entryClone = reversal.reversedOf.getValue(original.initLoc)
    val error = reversal.procedure.errorLoc.get()
    assertFalse(entryClone.error)
    assertTrue(error !in reversal.originalOf && error.outgoingEdges.isEmpty())
    assertEquals(entryClone, error.incomingEdges.single().source)
  }

  @Test
  fun `a reversed path maps back to the original path`() {
    val xcfa = counterXcfa(bad = 1)
    val original = xcfa.procedures.single()
    val reversal = reverseProgram(xcfa)
    val path = mutableListOf<XcfaEdge>()
    var location = reversal.procedure.initLoc
    while (location.outgoingEdges.isNotEmpty()) {
      val edge = location.outgoingEdges.single()
      path += edge
      location = edge.target
    }

    val originalPath = reversal.originalPath(path)
    assertEquals(original.initLoc, originalPath.first().source)
    assertTrue(originalPath.last().target.error)
    assertTrue(originalPath.zipWithNext().all { (a, b) -> a.target == b.source })
  }

  @Test
  fun `the violation conditions of the reversed program are strongest postconditions`() {
    val reachable = counterXcfa(bad = 1)
    val reversal = reverseProgram(reachable)
    val procedure = reachable.procedures.single()
    val x = procedure.intVar("x").ref
    val y = procedure.intVar("y").ref
    // A single state, so implication and joint satisfiability make the existential condition equal
    val single = And(Eq(x, Int(1)), Eq(y, Int(2)))
    val condition = reachableAtError(reversal)
    assertTrue(operators.isLeq(condition, single) && !operators.isUnsat(And(condition, single))) {
      "$condition"
    }

    assertTrue(operators.isUnsat(reachableAtError(reverseProgram(counterXcfa(bad = 2)))))
  }

  @Test
  fun `havocs and branches are reversed exactly`() {
    val xcfa =
      xcfa("havoc") {
        val main =
          procedure("main") {
            "x" type Int()
            "y" type Int()
            (init to "branch") { havoc("y") }
            ("branch" to "big") { assume("(> y 5)") }
            ("branch" to "small") { assume("(< y 0)") }
            ("big" to "join") { "x" assign "y" }
            ("small" to "join") { "x" assign "(- 0 y)" }
            ("join" to err) { nop() }
          }
        main.start()
      }
    val procedure = xcfa.procedures.single()
    val x = procedure.intVar("x").ref
    val y = procedure.intVar("y").ref

    assertEquivalent(
      Or(And(Gt(y, Int(5)), Eq(x, y)), And(Lt(y, Int(0)), Eq(x, Neg(y)))),
      reachableAtError(reverseProgram(xcfa)),
    )
  }

  @Test
  fun `a label without an exact reversal is rejected`() {
    val xcfa =
      xcfa("fence") {
        val main = procedure("main") { (init to err) { atomic_begin() } }
        main.start()
      }
    assertThrows<UnsupportedOperationException> { reverseProgram(xcfa) }
  }

  /**
   * States of a run without the error target may hold the entry's, so they are not complemented.
   */
  @Test
  fun `backward invariants come only from runs that kept the error as a target`() {
    val reversal = reverseProgram(counterXcfa(bad = 1))
    val procedure = reversal.procedure
    val error = procedure.errorLoc.get()
    val block = Block("R", procedure.initLoc, error, procedure.locs, procedure.edges)
    val graph = BlockGraph.fromBlocksWithoutEdges(listOf(block))
    val everywhere = procedure.locs.associateWith { listOf<Expr<BoolType>>(True()) }
    val targetless =
      DssBlockWitness(everywhere, emptyList(), emptyList(), errorFreeInvariants = null)

    val forward = combineInvariants(procedure, graph, mapOf("R" to targetless)).invariants
    assertTrue(forward.values.all { it == listOf(True()) }) { "$forward" }
    val dropped = backwardInvariants(reversal, graph, mapOf("R" to targetless)).invariants
    assertTrue(dropped.values.all { it == null }) { "$dropped" }

    val kept = targetless.copy(errorFreeInvariants = everywhere)
    val complemented = backwardInvariants(reversal, graph, mapOf("R" to kept)).invariants
    assertTrue(complemented.values.any { it != null }) { "$complemented" }
  }
}
