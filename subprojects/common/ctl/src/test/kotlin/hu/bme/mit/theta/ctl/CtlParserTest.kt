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
package hu.bme.mit.theta.ctl

import hu.bme.mit.delta.mdd.MddInterpreter
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr
import hu.bme.mit.theta.analysis.algorithm.mdd.ctl.CtlExpr
import hu.bme.mit.theta.analysis.algorithm.mdd.ctl.MddCtlChecker
import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Add
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Lt
import hu.bme.mit.theta.core.type.anytype.Exprs.Prime
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Or
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.solver.SolverPool
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertFalse
import org.junit.jupiter.api.Assertions.assertThrows
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

class CtlParserTest {

  private val x = Decls.Var("x", IntType.getInstance())
  private val vars = listOf(x)

  private fun parse(s: String): CtlExpr = CtlParser.parse(s, vars)

  // --- pure parsing (no MDD backend) ----------------------------------------------------------

  @Test
  fun parsesPrimitivesAndAtoms() {
    assertEquals(CtlExpr.EX(CtlExpr.Atom(Eq(x.ref, Int(1)))), parse("EX x = 1"))
    assertEquals(CtlExpr.EG(CtlExpr.Atom(Lt(x.ref, Int(3)))), parse("EG x < 3"))
    assertEquals(
      CtlExpr.EU(CtlExpr.Atom(Lt(x.ref, Int(3))), CtlExpr.Atom(Eq(x.ref, Int(3)))),
      parse("E[ x < 3 U x = 3 ]"),
    )
  }

  @Test
  fun parsesBooleanCombinatorsAtFormulaLevel() {
    // `&` binds tighter than `|`; atoms are relational, so this is Or(And(a,b), c)
    val expected =
      CtlExpr.Or(
        CtlExpr.And(CtlExpr.Atom(Lt(x.ref, Int(3))), CtlExpr.Atom(Eq(x.ref, Int(1)))),
        CtlExpr.Atom(Eq(x.ref, Int(2))),
      )
    assertEquals(expected, parse("x < 3 & x = 1 | x = 2"))
  }

  @Test
  fun desugarsImplicationAndNegation() {
    // a -> b == !a | b
    assertEquals(
      CtlExpr.Or(CtlExpr.Not(CtlExpr.Atom(Eq(x.ref, Int(0)))), CtlExpr.Atom(Eq(x.ref, Int(1)))),
      parse("x = 0 -> x = 1"),
    )
    assertEquals(CtlExpr.Not(CtlExpr.EX(CtlExpr.Atom(Eq(x.ref, Int(1))))), parse("!EX x = 1"))
  }

  @Test
  fun parsesArithmeticInsideAtoms() {
    assertEquals(CtlExpr.Atom(Lt(Add(x.ref, Int(1)), Int(5))), parse("x + 1 < 5"))
  }

  @Test
  fun rejectsGarbageAndUnknownVariables() {
    assertThrows(CtlParseException::class.java) { parse("EX EX") }
    assertThrows(IllegalStateException::class.java) { parse("y = 0") }
  }

  // --- end to end: parse -> check (same counter model as MddCtlCheckerTest) --------------------

  private fun <T> withChecker(block: (MddCtlChecker) -> T): T {
    val init = Eq(x.ref, Int(0))
    val trans =
      Or(
        And(Lt(x.ref, Int(3)), Eq(Prime(x.ref), Add(x.ref, Int(1)))),
        And(Eq(x.ref, Int(3)), Eq(Prime(x.ref), x.ref)),
      )
    val monolithicExpr = MonolithicExpr(init, trans, True())
    SolverPool(Z3LegacySolverFactory.getInstance()).use { pool ->
      return block(MddCtlChecker(monolithicExpr, pool, NullLogger.getInstance()))
    }
  }

  @Test
  fun parsedFormulasCheckCorrectly() = withChecker { c ->
    assertTrue(c.isSatisfied(parse("EF x = 3")))
    assertTrue(c.isSatisfied(parse("AF x = 3")))
    assertTrue(c.isSatisfied(parse("EX x = 1")))
    assertFalse(c.isSatisfied(parse("EX x = 2")))
    assertFalse(c.isSatisfied(parse("EG x = 3")))
    assertTrue(c.isSatisfied(parse("AG x <= 3")))
    assertFalse(c.isSatisfied(parse("AG !(x = 2)")))
    assertTrue(c.isSatisfied(parse("E[ x < 3 U x = 3 ]")))
    // EF x=3 set has all 4 states
    assertEquals(4L, MddInterpreter.calculateNonzeroCount(c.check(parse("EF x = 3"))))
  }
}
