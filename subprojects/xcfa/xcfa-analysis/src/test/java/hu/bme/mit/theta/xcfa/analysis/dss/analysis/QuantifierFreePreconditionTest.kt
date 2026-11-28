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

import hu.bme.mit.theta.core.decl.Decls.Param
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Exists
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And
import hu.bme.mit.theta.core.type.inttype.IntExprs.Gt
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntExprs.Lt
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.xcfa.analysis.dss.decomposition.LinearBlockDecomposition
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertFalse
import org.junit.jupiter.api.Assertions.assertNotSame
import org.junit.jupiter.api.Assertions.assertSame
import org.junit.jupiter.api.Test

/** The block program a quantifier-free fallback solver gets ([withQuantifierFreePrecondition]). */
class QuantifierFreePreconditionTest {

  private val program: XCFA =
    xcfa("quantifier-free-precondition") {
      val main =
        procedure("main") {
          "x" type Int()
          (init to "branch") { "x" assign "5" }
          ("branch" to "checkA") { assume("(< x 10)") }
          ("branch" to "checkB") { assume("(>= x 10)") }
          ("checkA" to final) { nop() }
          ("checkB" to err) { nop() }
        }
      main.start()
    }

  private val procedure = program.procedures.single()

  @Suppress("UNCHECKED_CAST")
  private val x = procedure.vars.single { it.name == "x" } as VarDecl<IntType>

  private val block =
    LinearBlockDecomposition().decompose(procedure).blocks.single { block ->
      block.locations.any { it.name == "checkB" }
    }

  private val p = Param("p", Int())
  private val positive = Gt(x.ref, Int(0))
  private val below = Exists(listOf(p), And(Lt(x.ref, p.ref), Lt(p.ref, Int(3))))

  private fun precondition(program: XCFA) =
    program.procedures.single().initLoc.outgoingEdges.single().getFlatLabels().map {
      ((it as StmtLabel).stmt as AssumeStmt).cond
    }

  @Test
  fun `the quantified part of the precondition is weakened away`() {
    val extraction = extractBlockXcfa(procedure, block, precondition = And(positive, below))

    val weakened = withQuantifierFreePrecondition(extraction.xcfa)

    assertNotSame(extraction.xcfa, weakened)
    assertEquals(listOf(positive), precondition(weakened))
    assertFalse(
      weakened.procedures.single().edges.any { e ->
        e.getFlatLabels().any {
          (it as? StmtLabel)?.stmt.let { s -> s is AssumeStmt && hasQuantifier(s.cond) }
        }
      }
    )
  }

  @Test
  fun `the copy keeps the locations and the other edges`() {
    val extraction = extractBlockXcfa(procedure, block, precondition = And(positive, below))
    val original = extraction.xcfa.procedures.single()

    val weakened = withQuantifierFreePrecondition(extraction.xcfa).procedures.single()

    assertEquals(original.locs, weakened.locs)
    assertEquals(
      original.edges.filter { it.source != original.initLoc }.toSet(),
      weakened.edges.filter { it.source != weakened.initLoc }.toSet(),
    )
  }

  @Test
  fun `a block program without quantifiers is kept as it is`() {
    val extraction = extractBlockXcfa(procedure, block, precondition = positive)

    assertSame(extraction.xcfa, withQuantifierFreePrecondition(extraction.xcfa))
  }
}
