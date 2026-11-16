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
package hu.bme.mit.theta.xcfa.passes

import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.passes.structure.DeterministicPass
import hu.bme.mit.theta.xcfa.passes.structure.NormalizePass
import hu.bme.mit.theta.xcfa.passes.structure.SimplifyExprsPass
import org.junit.jupiter.api.Assertions.assertFalse
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

class SimplifyExprsPassInvariantsTest {

  @Test
  fun constantIsRecordedOnlyAfterItsAssignment() {
    val parseContext = ParseContext()
    val builder =
      XcfaBuilder("")
        .procedure("main") {
          "r" type Int()
          "x" type Int()
          (init to "L1") { "r".assign("0") }
          ("L1" to "L2") { "x".assign("5") }
          ("L2" to final) { "r".assign("x") }
        }
        .builder
    simplify(builder, parseContext)

    assertFalse("x" in parseContext.passInvariantVars("L1"))
    assertTrue(
      Eq(builder.getVars().first { it.name == "x" }.ref, Int(5)) in
        ExprUtils.getConjuncts(parseContext.passInvariant("L2"))
    )
  }

  @Test
  fun constantIsNotRecordedWhereSomePathSkipsItsAssignment() {
    val parseContext = ParseContext()
    val builder =
      XcfaBuilder("")
        .procedure("main") {
          "c" type Int()
          "x" type Int()
          (init to "L1") { havoc("c") }
          ("L1" to "L2") {
            assume("(< c 0)")
            "x".assign("5")
          }
          ("L1" to "L2") { assume("(>= c 0)") }
          ("L2" to final) { "c".assign("0") }
        }
        .builder
    simplify(builder, parseContext)

    assertFalse("x" in parseContext.passInvariantVars("L2"))
  }

  private fun simplify(builder: XcfaProcedureBuilder, parseContext: ParseContext) {
    listOf(
        NormalizePass(),
        DeterministicPass(),
        SimplifyExprsPass(parseContext, recordPassInvariants = true),
      )
      .forEach { it.runChecked(builder) }
  }

  private fun ParseContext.passInvariant(location: String): Expr<BoolType> =
    ExprUtils.simplify(
      And(metadata.getMetadataValue(location, "passInvariants").get() as List<Expr<BoolType>>)
    )

  private fun ParseContext.passInvariantVars(location: String) =
    ExprUtils.getVars(passInvariant(location)).map { it.name }
}
