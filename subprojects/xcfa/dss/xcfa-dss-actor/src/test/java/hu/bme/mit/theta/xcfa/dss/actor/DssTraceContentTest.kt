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
package hu.bme.mit.theta.xcfa.dss.actor

import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolExprs.False
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Not
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Or
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.inttype.IntExprs.Gt
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntExprs.Lt
import org.junit.jupiter.api.AfterEach
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test

class DssTraceContentTest {

  private val x = Var("x", Int())
  private val y = Var("y", Int())
  private val xPos = Gt(x.ref, Int(0))
  private val formula = Or(And(xPos, Lt(y.ref, Int(1))), Not(xPos))

  @AfterEach fun disableTrace() = DssTrace.disable()

  private fun fields(content: Array<Pair<String, Any?>>) = content.toMap()

  @Test
  fun `content counts disjuncts, distinct atoms and variables`() {
    val f = fields(traceContent(formula))
    assertEquals(2, f["disj"])
    assertEquals(2, f["atoms"])
    assertEquals(2, f["vars"])
    assertEquals(0, f["aux"])
    assertEquals(false, f["top"])
    assertEquals(null, f["expr"])
  }

  @Test
  fun `true is one top disjunct and false has none`() {
    assertEquals(true, fields(traceContent(True()))["top"])
    assertEquals(0, fields(traceContent(False()))["disj"])
  }

  @Test
  fun `with expressions the formula comes last`() {
    DssTrace.enable(expressions = true) {}
    val content = traceContent(formula)
    assertEquals("expr" to formula.toString(), content.last())
  }
}
