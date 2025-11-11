/*
 *  Copyright 2025 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.xcfa.analysis

import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr
import hu.bme.mit.theta.c2xcfa.getXcfaFromC
import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.abstracttype.EqExpr
import hu.bme.mit.theta.core.type.abstracttype.NeqExpr
import hu.bme.mit.theta.core.type.anytype.PrimeExpr
import hu.bme.mit.theta.core.type.booltype.AndExpr
import hu.bme.mit.theta.core.type.booltype.TrueExpr
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.analysis.monolithic.XcfaMultiThreadToMonolithicAdapter
import hu.bme.mit.theta.xcfa.analysis.monolithic.XcfaSingleThreadToMonolithicAdapter
import hu.bme.mit.theta.xcfa.analysis.oc.vars
import hu.bme.mit.theta.xcfa.model.StartLabel
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.utils.collectVars
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import org.junit.jupiter.api.Assertions.*
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.MethodSource

class XcfaMonolithicTest {

  companion object {

    private fun genericTest(xcfa: XCFA, parseContext: ParseContext, monolithic: MonolithicExpr) {
      operator fun Expr<*>.contains(other: (Expr<*>) -> Boolean): Boolean =
        if (other(this)) true else ops.any { other in it }

      operator fun Expr<*>.contains(other: Expr<*>): Boolean = { other == it } in this

      monolithic.ctrlVars.forEach { ctrl ->
        assertTrue(
          Eq(cast(ctrl.ref, Int()), Int(0)) in monolithic.initExpr ||
            Eq(cast(ctrl.ref, Int()), Int(-1)) in monolithic.initExpr,
          "Initial expression does not contain expected control variable assignment.",
        )
        assertTrue(ctrl in monolithic.vars)
      }

      assertEquals(
        1,
        monolithic.ctrlVars.count { ctrl ->
          Eq(cast(ctrl.ref, Int()), Int(0)) in monolithic.initExpr
        },
        "There should be exactly one control variable initialized to 0 (the location var of the init thread).",
      )

      val allVars =
        xcfa.procedures.flatMap { p -> p.edges.flatMap { e -> e.label.collectVars() } } +
          monolithic.ctrlVars
      allVars.forEach { v ->
        assertTrue(
          monolithic.vars.any { v.name in it.name },
          "Variable ${v.name} from the XCFA is missing in the monolithic expression.",
        )
      }

      if (parseContext.multiThreading) {
        assertInstanceOf(AndExpr::class.java, monolithic.propExpr)
        assertEquals(
          xcfa.procedures.count {
            it.errorLoc.isPresent && it.errorLoc.get().incomingEdges.isNotEmpty()
          },
          monolithic.propExpr.ops.filter { it !is TrueExpr }.size,
        )
      } else {
        assertInstanceOf(NeqExpr::class.java, monolithic.propExpr)
      }

      assertInstanceOf(AndExpr::class.java, monolithic.transExpr)
      monolithic.transExpr.ops.forEach { t ->
        assertTrue(
          { expr ->
            expr is AndExpr &&
              expr.ops.first().let {
                it is EqExpr<*> && it.vars.size == 1 && "__loc_" in it.leftOp.vars.single().name
              } &&
              expr.ops.any {
                it is EqExpr<*> &&
                  it.vars.size == 1 &&
                  it.leftOp is PrimeExpr<*> &&
                  "__loc_" in it.leftOp.ops.first().vars.single().name
              } &&
              expr.ops.any {
                it is EqExpr<*> &&
                  it.vars.size == 1 &&
                  it.leftOp is PrimeExpr<*> &&
                  "__edge_" == it.leftOp.ops.first().vars.single().name
              }
          } in t
        )
      }
    }

    @JvmStatic
    private fun data(): Collection<String> {
      return listOf(
        "/00assignment.c",
        "/01function.c",
        "/02functionparam.c",
        "/03nondetfunction.c",
        "/04multithread.c",
        "/07mutex.c",
        "/10ptr.c",
      )
    }
  }

  @ParameterizedTest
  @MethodSource("data")
  fun testMonolithicExprTransformation(program: String) {
    println("Testing $program for XCFA to monolithic expression transformation.")
    val stream = javaClass.getResourceAsStream(program)
    val property = XcfaProperty(ErrorDetection.ERROR_LOCATION)
    val xcfa =
      getXcfaFromC(stream!!, ParseContext(), false, property, NullLogger.getInstance()).first
    val multithread =
      xcfa.procedures.any { p ->
        p.edges.any { e -> e.getFlatLabels().filterIsInstance<StartLabel>().isNotEmpty() }
      }
    val parseContext = ParseContext().apply { this.multiThreading = multithread }

    val adapter =
      if (multithread) {
        XcfaMultiThreadToMonolithicAdapter(xcfa, property.verifiedProperty, parseContext, true)
      } else {
        XcfaSingleThreadToMonolithicAdapter(xcfa, property.verifiedProperty, parseContext, true)
      }
    val monolithic = adapter.monolithicExpr

    genericTest(xcfa, parseContext, monolithic)
  }
}
