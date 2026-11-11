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
package hu.bme.mit.theta.xcfa.passes.witness

import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.type.anytype.IteExpr
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.xcfa.ThetaHelperDeclarations.Witness.SEGMENT_COUNTER
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

class WitnessOptimizerTest {

  @Test
  fun branchValuesDoNotLeakIntoTheMerge() {
    val builder = XcfaBuilder("").also { it.global { SEGMENT_COUNTER type Int() init "0" } }
    val procedure =
      builder
        .procedure("main") {
          "c" type Bool()
          "r" type Int()
          "p" type Int()
          (init to "L0") {
            SEGMENT_COUNTER.assign("(ite (= $SEGMENT_COUNTER 0) 1 $SEGMENT_COUNTER)")
          }
          ("L0" to "L1") {
            assume("c")
            "r".assign("0")
          }
          ("L0" to "L1") {
            assume("(not c)")
            "r".assign("1")
          }
          ("L1" to final) { "p".assign("r") }
        }
        .builder
    val optimized = WitnessOptimizer(listOf(), ParseContext()).runChecked(procedure)

    val assign = optimized.finalLoc.get().incomingEdges.single().getFlatLabels().single()
    val expr = ((assign as StmtLabel).stmt as AssignStmt<*>).expr
    assertEquals("r", (expr as RefExpr<*>).decl.name)
  }

  @Test
  fun aLaterSegmentIsNotForcedBeforeTheNextOne() {
    val builder = XcfaBuilder("").also { it.global { SEGMENT_COUNTER type Int() init "0" } }
    val procedure =
      builder
        .procedure("main") {
          // the update of segment 1 is reached before that of segment 0, e.g. at a loop head
          (init to "L0") {
            SEGMENT_COUNTER.assign("(ite (= $SEGMENT_COUNTER 1) 2 $SEGMENT_COUNTER)")
          }
          ("L0" to final) {
            SEGMENT_COUNTER.assign("(ite (= $SEGMENT_COUNTER 0) 1 $SEGMENT_COUNTER)")
          }
        }
        .builder
    val optimized = WitnessOptimizer(listOf(), ParseContext()).runChecked(procedure)

    val first = optimized.initLoc.outgoingEdges.single().getFlatLabels().single()
    assertTrue(((first as StmtLabel).stmt as AssignStmt<*>).expr is IteExpr<*>)
    val second = optimized.finalLoc.get().incomingEdges.single().getFlatLabels()
    assertEquals(
      listOf("(assume (= $SEGMENT_COUNTER 0))", "(assign $SEGMENT_COUNTER 1)"),
      second.map { (it as StmtLabel).stmt.toString() },
    )
  }
}
