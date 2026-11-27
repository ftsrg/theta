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

import hu.bme.mit.theta.analysis.Cex
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And
import hu.bme.mit.theta.core.type.inttype.IntExprs.Eq
import hu.bme.mit.theta.core.type.inttype.IntExprs.Geq
import hu.bme.mit.theta.core.type.inttype.IntExprs.Gt
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntExprs.Leq
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.solver.SolverManager
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.analysis.dss.actor.DEFAULT_DSS_SOLVER
import hu.bme.mit.theta.xcfa.analysis.dss.ensureDefaultSolversRegistered
import hu.bme.mit.theta.xcfa.analysis.proof.LocationInvariants
import hu.bme.mit.theta.xcfa.cli.checkers.getCegarChecker
import hu.bme.mit.theta.xcfa.cli.params.getDefaultPredCegarConfig
import hu.bme.mit.theta.xcfa.model.*
import org.junit.jupiter.api.Assertions.assertFalse
import org.junit.jupiter.api.Assertions.assertNull
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.BeforeAll
import org.junit.jupiter.api.Test

class TreePostconditionTest {

  companion object {

    @JvmStatic
    @BeforeAll
    fun registerSolvers() {
      ensureDefaultSolversRegistered(getDefaultPredCegarConfig(), NullLogger.getInstance())
    }
  }

  private val solverFactory by lazy { SolverManager.resolveSolverFactory(DEFAULT_DSS_SOLVER) }
  private val operators by lazy { DssPredicateOperators(solverFactory) }

  /** `x := y; x := x + 1`: x > y holds at the end, but not in between. */
  private val straightLine: XCFA =
    xcfa("tree-straight") {
      val main =
        procedure("main") {
          "x" type Int()
          "y" type Int()
          (init to "a") { "x" assign "y" }
          ("a" to "b") { "x" assign "(+ x 1)" }
          ("b" to final) { nop() }
        }
      main.start()
    }

  /**
   * Two branches meeting at the exit, `x := y; x := x + 1` and `x := y; x := x + 2`: x > y at the
   * end of both, but not in between, so both exit nodes have the abstract state true.
   */
  private val diamond: XCFA =
    xcfa("tree-diamond") {
      val main =
        procedure("main") {
          "x" type Int()
          "y" type Int()
          (init to "c1") { assume("(> y 0)") }
          (init to "c2") { assume("(<= y 0)") }
          ("c1" to "b1") { "x" assign "y" }
          ("c2" to "b2") { "x" assign "y" }
          ("b1" to final) { "x" assign "(+ x 1)" }
          ("b2" to final) { "x" assign "(+ x 2)" }
        }
      main.start()
    }

  /** `x := 0; while (x < 10) x := x + 1`: x == 10 at the end. */
  private val loop: XCFA =
    xcfa("tree-loop") {
      val main =
        procedure("main") {
          "x" type Int()
          (init to "h") { "x" assign "0" }
          ("h" to "body") { assume("(< x 10)") }
          ("body" to "h") { "x" assign "(+ x 1)" }
          ("h" to final) { assume("(>= x 10)") }
        }
      main.start()
    }

  @Suppress("UNCHECKED_CAST")
  private fun XCFA.int(name: String) =
    procedures.single().vars.single { it.name == name } as VarDecl<IntType>

  private fun XCFA.finalLocation() = procedures.single().finalLoc.get()

  private fun prove(
    xcfa: XCFA,
    predicates: Set<Expr<BoolType>>,
    keepProofTree: Boolean = true,
  ): LocationInvariants {
    val result =
      runWorkerConfig(
        xcfa,
        checkerFactory = { x ->
          getCegarChecker(
            x,
            emptySet(),
            ParseContext(),
            getDefaultPredCegarConfig(),
            NullLogger.getInstance(),
            keepProofTree = keepProofTree,
          )
        },
        initialPrecision = getPredPrec(predicates),
      )
    check(result.isSafe) { "Expected a safe result, got $result" }
    return result.asSafe().proof
  }

  private fun equivalent(a: Expr<BoolType>, b: Expr<BoolType>) =
    operators.isLeq(a, b) && operators.isLeq(b, a)

  @Test
  fun `the tree keeps what the abstract states lose between two locations`() {
    val x = straightLine.int("x")
    val y = straightLine.int("y")
    val xAboveY = Gt(x.ref, y.ref)
    val proof = prove(straightLine, setOf(xAboveY))
    val exit = straightLine.finalLocation()

    val plain = packPostcondition(SafetyResult.safe<LocationInvariants, Cex>(proof), exit)
    val tree = packTreePostcondition(proof, exit, setOf(xAboveY), solverFactory)

    assertTrue(equivalent(plain, True()), "plain postcondition: $plain")
    assertTrue(tree != null && equivalent(tree, xAboveY), "tree postcondition: $tree")
  }

  @Test
  fun `a path out of a loop starts from the covering loop head, not from the root`() {
    val x = loop.int("x")
    val predicates = setOf(Geq(x.ref, Int(0)), Leq(x.ref, Int(10)))
    val proof = prove(loop, predicates)
    val exit = loop.finalLocation()
    val xIsTen = Eq(x.ref, Int(10))

    val tree = packTreePostcondition(proof, exit, predicates + xIsTen, solverFactory)!!
    val plain = packPostcondition(SafetyResult.safe<LocationInvariants, Cex>(proof), exit)

    // From the root, the exit path would be x == 0 && x >= 10: infeasible, an unsound False
    assertFalse(operators.isUnsat(And(tree, xIsTen)), "tree postcondition: $tree")
    assertTrue(operators.isLeq(tree, plain), "tree $tree, plain $plain")
  }

  @Test
  fun `without a kept tree there is no tree postcondition`() {
    val x = straightLine.int("x")
    val proof = prove(straightLine, setOf(Gt(x.ref, Int(0))), keepProofTree = false)

    assertNull(proof.tree)
    assertNull(
      packTreePostcondition(proof, straightLine.finalLocation(), emptySet(), solverFactory)
    )
  }

  @Test
  fun `with exact exits, paths meeting at the exit keep their own paths`() {
    val x = diamond.int("x")
    val y = diamond.int("y")
    val xAboveY = Gt(x.ref, y.ref)
    val proof = prove(diamond, setOf(xAboveY))
    val exit = diamond.finalLocation()
    val exits =
      proof.tree!!.nodes.filter {
        (it.state as XcfaState<*>).processes.values.singleOrNull()?.locs?.peek() == exit
      }
    check(exits.any { it.isCovered }) { "Expected one exit node to cover the other" }

    val anchored = packTreePostcondition(proof, exit, setOf(xAboveY), solverFactory)!!
    val exact =
      packTreePostcondition(proof, exit, setOf(xAboveY), solverFactory, exactExits = true)!!

    assertTrue(equivalent(anchored, True()), "anchored at the covering exit node: $anchored")
    assertTrue(equivalent(exact, xAboveY), "exact exits: $exact")
  }

  @Test
  fun `exact exits stay sound out of a loop`() {
    val x = loop.int("x")
    val predicates = setOf(Geq(x.ref, Int(0)), Leq(x.ref, Int(10)))
    val proof = prove(loop, predicates)
    val exit = loop.finalLocation()
    val xIsTen = Eq(x.ref, Int(10))

    val exact =
      packTreePostcondition(proof, exit, predicates + xIsTen, solverFactory, exactExits = true)!!

    assertFalse(operators.isUnsat(And(exact, xIsTen)), "exact exits: $exact")
  }
}
