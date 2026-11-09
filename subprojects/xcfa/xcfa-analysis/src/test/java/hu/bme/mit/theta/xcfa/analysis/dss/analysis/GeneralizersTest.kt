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
import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And
import hu.bme.mit.theta.core.type.inttype.IntExprs.*
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.solver.SolverManager
import hu.bme.mit.theta.xcfa.analysis.dss.ensureDefaultSolversRegistered
import hu.bme.mit.theta.xcfa.cli.params.getDefaultPredCegarConfig
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertNull
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.BeforeAll
import org.junit.jupiter.api.Test

/** The semantic generalizer and the ways [Generalizers] combines methods. */
class GeneralizersTest {

  companion object {
    @JvmStatic
    @BeforeAll
    fun registerSolvers() {
      ensureDefaultSolversRegistered(getDefaultPredCegarConfig(), NullLogger.getInstance())
    }
  }

  private val operators by lazy { DssPredicateOperators(SolverManager.resolveSolverFactory("Z3")) }

  private val x = Var("x", Int())
  private val n = Var("n", Int())

  /** The states that matter are `x >= 0`: a condition is unreachable if it excludes them. */
  private val reachable = Geq(x.ref, Int(0))

  private val context by lazy {
    GeneralizationContext(operators::isUnsat) { operators.isUnsat(And(reachable, it)) }
  }

  /** The k-th condition of the loop head: `x == -2 - k && n >= -1`. */
  private fun condition(k: Int): Expr<BoolType> = And(Eq(x.ref, Int(-2 - k)), Geq(n.ref, Int(-1)))

  @Test
  fun `the first condition already generalizes to every later one`() {
    val candidate =
      requireNotNull(SemanticGeneralizer(gas = 2).generalize("B", condition(0), context))
    for (k in 0..5) {
      assertTrue(operators.isLeq(condition(k), candidate.condition), "${candidate.condition}")
    }
    assertTrue(operators.isUnsat(And(reachable, candidate.condition)), "${candidate.condition}")
    assertTrue(n !in ExprUtils.getVars(candidate.condition), "${candidate.condition}")
  }

  @Test
  fun `a reachable condition is not generalized`() {
    assertNull(SemanticGeneralizer(gas = 2).generalize("B", Eq(x.ref, Int(3)), context))
  }

  @Test
  fun `without a reachability check there is no candidate`() {
    val unchecked = GeneralizationContext(operators::isUnsat)
    assertNull(SemanticGeneralizer(gas = 2).generalize("B", condition(0), unchecked))
  }

  @Test
  fun `a failed candidate is not proposed again, and a sender runs out of gas`() {
    val generalizer = SemanticGeneralizer(gas = 2)
    val first = requireNotNull(generalizer.generalize("B", condition(0), context))
    generalizer.failed(first)
    assertNull(generalizer.generalize("B", condition(0), context))
    val other = requireNotNull(generalizer.generalize("B", Eq(x.ref, Int(-7)), context))
    generalizer.failed(other)
    assertNull(generalizer.generalize("B", Eq(x.ref, Int(-9)), context), "B is out of gas")
    assertTrue(generalizer.generalize("C", Eq(x.ref, Int(-9)), context) != null)
  }

  private fun generalizers(combination: DssGeneralizerCombination) =
    Generalizers(
      listOf(DssGeneralizerKind.GSPACER, DssGeneralizerKind.SEMANTIC),
      combination,
      gas = 2,
    )

  /** Records conditions 0..[last] of sender B and generalizes the last one. */
  private fun Generalizers.after(last: Int): Generalization? {
    (0..last).forEach { record("B", condition(it)) }
    return generalize(listOf("B" to condition(last)), context)
  }

  @Test
  fun `FIRST takes GSPACER once it has a history, and SEMANTIC before`() {
    assertEquals(
      listOf(DssGeneralizerKind.SEMANTIC),
      generalizers(DssGeneralizerCombination.FIRST).after(0)?.kinds,
    )
    assertEquals(
      listOf(DssGeneralizerKind.GSPACER),
      generalizers(DssGeneralizerCombination.FIRST).after(1)?.kinds,
    )
  }

  @Test
  fun `UNION and CHAIN use every method, and CHAIN weakens GSPACER's result`() {
    val union = requireNotNull(generalizers(DssGeneralizerCombination.UNION).after(1))
    assertEquals(listOf(DssGeneralizerKind.GSPACER, DssGeneralizerKind.SEMANTIC), union.kinds)
    val chain = requireNotNull(generalizers(DssGeneralizerCombination.CHAIN).after(1))
    assertEquals(listOf(DssGeneralizerKind.GSPACER, DssGeneralizerKind.SEMANTIC), chain.kinds)
    val gspacer = requireNotNull(generalizers(DssGeneralizerCombination.FIRST).after(1))
    assertTrue(operators.isLeq(gspacer.condition, chain.condition), "${chain.condition}")
    assertTrue(operators.isUnsat(And(reachable, chain.condition)), "${chain.condition}")
  }
}
