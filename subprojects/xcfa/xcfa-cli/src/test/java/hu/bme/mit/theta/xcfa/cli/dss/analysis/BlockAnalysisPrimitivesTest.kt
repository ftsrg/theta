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
package hu.bme.mit.theta.xcfa.cli.dss.analysis

import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.Stmts.Assign
import hu.bme.mit.theta.core.stmt.Stmts.Assume
import hu.bme.mit.theta.core.stmt.Stmts.Havoc
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Not
import hu.bme.mit.theta.core.type.inttype.IntExprs.*
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.solver.SolverManager
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.*
import hu.bme.mit.theta.xcfa.analysis.dss.decomposition.Block
import hu.bme.mit.theta.xcfa.analysis.dss.decomposition.LinearBlockDecomposition
import hu.bme.mit.theta.xcfa.cli.checkers.getCegarChecker
import hu.bme.mit.theta.xcfa.cli.dss.ensureDefaultSolversRegistered
import hu.bme.mit.theta.xcfa.cli.params.getDefaultPredCegarConfig
import hu.bme.mit.theta.xcfa.model.*
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertFalse
import org.junit.jupiter.api.Assertions.assertThrows
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.BeforeAll
import org.junit.jupiter.api.Test

class BlockAnalysisPrimitivesTest {

  companion object {

    @JvmStatic
    @BeforeAll
    fun registerSolvers() {
      ensureDefaultSolversRegistered(getDefaultPredCegarConfig(), NullLogger.getInstance())
    }
  }

  private val operators by lazy { DssPredicateOperators(SolverManager.resolveSolverFactory("Z3")) }

  private val x = Var("x", Int())
  private val y = Var("y", Int())

  private fun equivalent(a: Expr<BoolType>, b: Expr<BoolType>) =
    operators.isLeq(a, b) && operators.isLeq(b, a)

  private fun check(xcfa: XCFA) =
    runWorkerConfig(
      xcfa,
      checkerFactory = { p ->
        getCegarChecker(
          p,
          emptySet(),
          ParseContext(),
          getDefaultPredCegarConfig(),
          NullLogger.getInstance(),
        )
      },
    )

  private fun loc(name: String, error: Boolean = false) =
    XcfaLocation(name, error = error, metadata = EmptyMetaData)

  /** A hand-built block: a chain of [labels] from `l0` to `lN`. */
  private fun chain(vararg labels: XcfaLabel): Block {
    val locations = (0..labels.size).map { loc("l$it") }
    val edges =
      labels.mapIndexed { i, label ->
        XcfaEdge(locations[i], locations[i + 1], label, EmptyMetaData).also {
          locations[i].outgoingEdges.add(it)
          locations[i + 1].incomingEdges.add(it)
        }
      }
    return Block("B", locations.first(), locations.last(), locations.toSet(), edges.toSet())
  }

  @Test
  fun `weakest preconditions of assumptions, assignments and sequences`() {
    val block =
      chain(
        SequenceLabel(listOf(StmtLabel(Assign(x, Add(x.ref, Int(1)))), NopLabel)),
        StmtLabel(Assume(Gt(x.ref, Int(3)))),
      )

    val vc = computeViolationCondition(block, mapOf(block.finalLocation to Lt(x.ref, Int(10))))

    assertTrue(equivalent(vc, And(Gt(x.ref, Int(2)), Lt(x.ref, Int(9)))), "$vc")
  }

  @Test
  fun `a nondeterministic choice is a disjunction`() {
    val block =
      chain(
        NondetLabel(setOf(StmtLabel(Assign(x, Int(1))), StmtLabel(Assign(x, Add(y.ref, Int(5))))))
      )

    val vc = computeViolationCondition(block, mapOf(block.finalLocation to Eq(x.ref, Int(7))))

    assertTrue(equivalent(vc, Eq(y.ref, Int(2))), "$vc")
  }

  @Test
  fun `a havoc is existentially quantified - the condition holds whatever the other variables are`() {
    val block = chain(StmtLabel(Havoc(x)))

    val vc = computeViolationCondition(block, mapOf(block.finalLocation to Gt(x.ref, y.ref)))

    assertEquals(1, DssAuxVars.collectVars(vc).size)
    assertFalse(x in ExprUtils.getVars(vc))
    assertFalse(operators.isUnsat(And(Eq(y.ref, Int(100)), vc)))
  }

  @Test
  fun `labels without a weakest-precondition rule are rejected`() {
    val block = chain(InvokeLabel("f", emptyList(), EmptyMetaData))

    assertThrows(UnsupportedOperationException::class.java) {
      computeViolationCondition(block, mapOf(block.finalLocation to True()))
    }
  }

  @Test
  fun `a target that cannot be reached gives an unsatisfiable condition`() {
    val block = chain(StmtLabel(Assign(x, Int(1))))

    val vc = computeViolationCondition(block, mapOf(block.finalLocation to Eq(x.ref, Int(2))))

    assertTrue(operators.isUnsat(vc))
  }

  /** `n` diamonds in a row, both arms with the same update, joined into one block. */
  private fun diamonds(n: Int): Block {
    val locations = mutableListOf(loc("d0"))
    val edges = mutableSetOf<XcfaEdge>()
    fun edge(from: XcfaLocation, to: XcfaLocation, label: XcfaLabel) {
      val e = XcfaEdge(from, to, label, EmptyMetaData)
      from.outgoingEdges.add(e)
      to.incomingEdges.add(e)
      edges.add(e)
    }
    repeat(n) { i ->
      val head = locations.last()
      val a = loc("a$i")
      val b = loc("b$i")
      val join = loc("d${i + 1}")
      edge(head, a, StmtLabel(Assume(Gt(y.ref, Int(i)))))
      edge(head, b, StmtLabel(Assume(Not(Gt(y.ref, Int(i))))))
      edge(a, join, StmtLabel(Assign(x, Add(x.ref, Int(1)))))
      edge(b, join, StmtLabel(Assign(x, Add(x.ref, Int(1)))))
      locations += listOf(a, b, join)
    }
    return Block("D", locations.first(), locations.last(), locations.toSet(), edges)
  }

  private fun size(expr: Expr<*>): Int = 1 + expr.ops.sumOf { size(it) }

  @Test
  fun `identical branches do not duplicate the condition`() {
    val ten = diamonds(10)
    val twenty = diamonds(20)

    val vc10 = computeViolationCondition(ten, mapOf(ten.finalLocation to Gt(x.ref, Int(100))))
    val vc20 = computeViolationCondition(twenty, mapOf(twenty.finalLocation to Gt(x.ref, Int(100))))

    assertTrue(equivalent(vc10, Gt(x.ref, Int(90))), "$vc10")
    assertTrue(size(vc20) < 4 * size(vc10), "${size(vc10)} vs ${size(vc20)}: should grow linearly")
  }

  /** init -(x := 0)-> branch; branch -(x < 10)-> final; branch -(x >= 10)-> err. */
  private fun branching(): XcfaProcedure =
    xcfa("primitives") {
        val main =
          procedure("main") {
            "x" type Int()
            (init to "branch") { "x" assign "0" }
            ("branch" to final) { assume("(< x 10)") }
            ("branch" to err) { assume("(>= x 10)") }
          }
        main.start()
      }
      .procedures
      .single()

  @Suppress("UNCHECKED_CAST")
  private fun XcfaProcedure.intVar(name: String) =
    vars.single { it.name == name } as VarDecl<IntType>

  private fun XcfaProcedure.errorBlock() =
    LinearBlockDecomposition().decompose(this).blocks.single { b -> b.locations.any { it.error } }

  @Test
  fun `a precondition becomes an assume edge in front of the block entry`() {
    val procedure = branching()
    val block = procedure.errorBlock()
    val px = procedure.intVar("x").ref

    val unreachable = extractBlockXcfa(procedure, block, precondition = Lt(px, Int(10)))
    val reachable = extractBlockXcfa(procedure, block)

    val entryEdge = unreachable.xcfa.procedures.single().initLoc.outgoingEdges.single()
    assertEquals(Assume(Lt(px, Int(10))), (entryEdge.label as StmtLabel).stmt)
    assertTrue(check(unreachable.xcfa).isSafe)
    assertTrue(check(reachable.xcfa).isUnsafe)
  }

  @Test
  fun `without specification targets, a block with an error location checks as safe`() {
    val procedure = branching()

    val extraction =
      extractBlockXcfa(procedure, procedure.errorBlock(), keepSpecificationTargets = false)

    assertFalse(extraction.xcfa.procedures.single().errorLoc.isPresent)
    assertTrue(check(extraction.xcfa).isSafe)
  }

  @Test
  fun `the auxiliary variables of a violation condition are havocked before it is assumed`() {
    val procedure = branching()
    val root = LinearBlockDecomposition().decompose(procedure).root
    val px = procedure.intVar("x").ref
    val havocY = chain(StmtLabel(Havoc(y)))
    val vc =
      computeViolationCondition(havocY, mapOf(havocY.finalLocation to Eq(px, Add(y.ref, Int(3)))))
    val auxVar = DssAuxVars.collectVars(vc).single()

    val extraction = extractBlockXcfa(procedure, root, violationCondition = vc)

    assertTrue(auxVar in extraction.xcfa.procedures.single().vars)
    val vcEdge = extraction.exitLocation.outgoingEdges.single()
    val labels = (vcEdge.label as SequenceLabel).labels
    assertEquals(listOf(StmtLabel(Havoc(auxVar)), StmtLabel(Assume(vc))), labels)
    assertTrue(vcEdge.target.error)
    assertTrue(check(extraction.xcfa).isUnsafe)
  }

  @Test
  fun `predicate operators decide satisfiability and implication`() {
    assertTrue(operators.isUnsat(And(Lt(x.ref, Int(0)), Gt(x.ref, Int(0)))))
    assertFalse(operators.isUnsat(Lt(x.ref, Int(0))))
    assertTrue(operators.isLeq(Lt(x.ref, Int(0)), Lt(x.ref, Int(5))))
    assertFalse(operators.isLeq(Lt(x.ref, Int(5)), Lt(x.ref, Int(0))))
    assertTrue(operators.isLeq(Lt(x.ref, Int(0)), True()))
  }

  @Test
  fun `collectPreds keeps the atoms over program variables only`() {
    val block = chain(StmtLabel(Havoc(x)))
    val vc = computeViolationCondition(block, mapOf(block.finalLocation to Gt(x.ref, y.ref)))

    val predicates = listOf(And(Lt(y.ref, Int(3)), vc)).collectPreds()

    assertEquals(setOf(Lt(y.ref, Int(3))), predicates)
  }
}
