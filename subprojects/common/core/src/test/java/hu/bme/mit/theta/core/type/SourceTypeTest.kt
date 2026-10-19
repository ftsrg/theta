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
package hu.bme.mit.theta.core.type

import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.inttype.IntExprs.Add
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntExprs.Lt
import hu.bme.mit.theta.core.type.inttype.IntType
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertNotSame
import org.junit.jupiter.api.Assertions.assertNull
import org.junit.jupiter.api.Assertions.assertSame
import org.junit.jupiter.api.Test

class SourceTypeTest {

  private data class Named(val name: String) : SourceType

  private val int = Named("int")
  private val x = Var("x", Int()).ref
  private val y = Var("y", Int()).ref

  @Test
  fun attachingCopiesAndKeepsEquality() {
    val plain = Add(x, Int(1))
    val typed = plain.withSourceType(int)
    assertNotSame(plain, typed)
    assertNull(plain.sourceType)
    assertSame(int, typed.sourceType)
    assertEquals(plain, typed)
    assertEquals(plain.hashCode(), typed.hashCode())
    assertSame(typed, typed.withSourceType(int))
  }

  @Test
  fun operandRewritesKeepTheType() {
    val typed = Lt(x, Int(1)).withSourceType(int) as IntLtExpr
    assertSame(int, typed.withOps(listOf(y, Int(2))).sourceType)
    assertSame(int, typed.with(y, Int(2)).sourceType)
    assertSame(int, typed.map { if (it == x) y else it }.sourceType)
    assertSame(typed, typed.withOps(typed.ops))
  }

  @Test
  fun rewritesKeepAnExplicitTypeOfTheNewNode() {
    val other = Named("char")
    val typed = Add(x, Int(1)).withSourceType(int) as IntAddExpr
    val rewritten = typed.withOps(listOf(y, Int(1)))
    assertSame(other, rewritten.withSourceType(other).sourceType)
    assertSame(int, rewritten.sourceType)
  }

  @Test
  fun booleanSingletonsStayUntyped() {
    assertSame(True(), True().withSourceType(int))
    assertNull(True().sourceType)
  }

  @Test
  fun foreignExpressionsCarryTheTypeToo() {
    val foreign =
      object : ForeignExpr<IntType>() {
        override val arity = 0
        override val type: IntType = Int()
        override val ops: List<Expr<*>> = listOf()

        override fun eval(valuation: Valuation) = Int(0)

        override fun withOps(ops: List<Expr<*>>) = this
      }
    assertSame(int, foreign.withSourceType(int).sourceType)
  }
}
