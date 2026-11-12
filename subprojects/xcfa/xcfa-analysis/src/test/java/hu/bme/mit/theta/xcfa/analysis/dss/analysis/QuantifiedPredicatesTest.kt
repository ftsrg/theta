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
import hu.bme.mit.theta.core.decl.Decls.Param
import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Exists
import hu.bme.mit.theta.core.type.booltype.BoolExprs.False
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Iff
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Imply
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Not
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Or
import hu.bme.mit.theta.core.type.inttype.IntExprs.*
import hu.bme.mit.theta.solver.ItpSolver
import hu.bme.mit.theta.solver.Solver
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.solver.SolverManager
import hu.bme.mit.theta.solver.UCSolver
import hu.bme.mit.theta.xcfa.analysis.dss.ensureDefaultSolversRegistered
import hu.bme.mit.theta.xcfa.cli.params.getDefaultPredCegarConfig
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertFalse
import org.junit.jupiter.api.Assertions.assertSame
import org.junit.jupiter.api.Assertions.assertThrows
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.BeforeAll
import org.junit.jupiter.api.Test

/** `--dss-quantified-predicates`: weakening and eliminating quantifiers, and the query fallback. */
class QuantifiedPredicatesTest {

  companion object {
    @JvmStatic
    @BeforeAll
    fun registerSolvers() {
      ensureDefaultSolversRegistered(getDefaultPredCegarConfig(), NullLogger.getInstance())
    }
  }

  /** Z3 takes quantifiers, so it can check what the transformations claim. */
  private val operators by lazy {
    DssPredicateOperators(SolverManager.resolveSolverFactory(QUANTIFIER_ELIMINATION_SOLVER))
  }

  private val x = Var("x", Int())
  private val y = Var("y", Int())
  private val p = Param("p", Int())

  /** `exists p. x < p < 3`, that is `x < 2`. */
  private val below = Exists(listOf(p), And(Lt(x.ref, p.ref), Lt(p.ref, Int(3))))

  /** The closed, false formula a `Z3:new` interpolant brought into `benchmark52_polynomial`. */
  private val closedFalse =
    Exists(
      listOf(p),
      And(
        Lt(Mul(Sub(p.ref, Int(1)), Sub(p.ref, Int(1))), Int(100)),
        Leq(Int(100), Mul(p.ref, p.ref)),
        Neq(p.ref, Int(10)),
      ),
    )

  private fun equivalent(a: Expr<BoolType>, b: Expr<BoolType>) =
    operators.isLeq(a, b) && operators.isLeq(b, a)

  @Test
  fun `a quantified subformula is weakened by its polarity`() {
    val positive = And(Gt(y.ref, Int(0)), below)
    val negative = And(Gt(y.ref, Int(0)), Not(below))
    val mixed = Or(Lt(y.ref, Int(0)), Iff(below, Gt(y.ref, Int(5))))
    val implied = Imply(below, Gt(y.ref, Int(5)))

    assertEquals(Gt(y.ref, Int(0)), withoutQuantifiers(positive))
    assertEquals(Gt(y.ref, Int(0)), withoutQuantifiers(negative))
    assertEquals(True(), withoutQuantifiers(mixed))
    assertEquals(True(), withoutQuantifiers(implied))
    for (expr in listOf(positive, negative, mixed, implied)) {
      val weakened = withoutQuantifiers(expr)
      assertFalse(hasQuantifier(weakened), "$weakened")
      assertTrue(operators.isLeq(expr, weakened), "$expr implies $weakened")
    }
  }

  @Test
  fun `a formula without quantifiers is left as it is`() {
    val plain = And(Gt(y.ref, Int(0)), Lt(x.ref, y.ref))
    assertSame(plain, withoutQuantifiers(plain))
    for (mode in DssQuantifiedPredicates.entries) {
      assertSame(plain, DssQuantifierCleaner(mode).clean(plain))
    }
  }

  @Test
  fun `elimination gives an equivalent quantifier-free formula`() {
    val cleaner = DssQuantifierCleaner(DssQuantifiedPredicates.ELIMINATE)
    val state = And(Gt(y.ref, Int(0)), below)

    val eliminated = cleaner.clean(state)
    val closed = cleaner.clean(And(Gt(y.ref, Int(0)), Not(closedFalse)))

    assertFalse(hasQuantifier(eliminated), "$eliminated")
    assertTrue(equivalent(eliminated, And(Gt(y.ref, Int(0)), Lt(x.ref, Int(2)))), "$eliminated")
    assertTrue(equivalent(closed, Gt(y.ref, Int(0))), "$closed")
  }

  @Test
  fun `only DROP and ELIMINATE change a quantified formula`() {
    val state = And(Gt(y.ref, Int(0)), below)
    assertSame(state, DssQuantifierCleaner(DssQuantifiedPredicates.KEEP).clean(state))
    assertSame(state, DssQuantifierCleaner(DssQuantifiedPredicates.FALLBACK).clean(state))
    assertEquals(Gt(y.ref, Int(0)), DssQuantifierCleaner(DssQuantifiedPredicates.DROP).clean(state))
  }

  @Test
  fun `a witness state only gets exact eliminations`() {
    val state = And(Gt(y.ref, Int(0)), below)
    for (mode in DssQuantifiedPredicates.entries - DssQuantifiedPredicates.ELIMINATE) {
      assertSame(state, DssQuantifierCleaner(mode).equivalent(state))
    }
    val eliminated = DssQuantifierCleaner(DssQuantifiedPredicates.ELIMINATE).equivalent(state)
    assertTrue(equivalent(eliminated, state), "$eliminated")
    assertFalse(hasQuantifier(eliminated), "$eliminated")
  }

  private object FailingSolverFactory : SolverFactory {
    override fun createSolver(): Solver = throw UnsupportedOperationException("no solver")

    override fun createUCSolver(): UCSolver = throw UnsupportedOperationException("no solver")

    override fun createItpSolver(): ItpSolver = throw UnsupportedOperationException("no solver")
  }

  @Test
  fun `a query the main solver fails on is decided by the fallback solver`() {
    val contradiction = And(Gt(x.ref, Int(0)), Lt(x.ref, Int(0)))
    val fallback = SolverManager.resolveSolverFactory(QUANTIFIER_ELIMINATION_SOLVER)

    assertThrows(DssUndecidedQueryException::class.java) {
      DssPredicateOperators(FailingSolverFactory).isUnsat(contradiction)
    }
    assertTrue(DssPredicateOperators(FailingSolverFactory, fallback).isUnsat(contradiction))
    assertThrows(DssUndecidedQueryException::class.java) {
      DssPredicateOperators(FailingSolverFactory, FailingSolverFactory).isUnsat(contradiction)
    }
  }

  @Test
  fun `a closed quantified formula reaching the queries is decided by a solver that takes it`() {
    assertTrue(operators.isUnsat(closedFalse))
    assertEquals(
      False(),
      DssQuantifierCleaner(DssQuantifiedPredicates.ELIMINATE).clean(closedFalse),
    )
  }
}
