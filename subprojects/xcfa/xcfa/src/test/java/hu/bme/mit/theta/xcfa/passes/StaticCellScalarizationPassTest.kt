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

import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.core.type.anytype.IteExpr
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.dereferences
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import org.junit.jupiter.api.AfterEach
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.BeforeEach
import org.junit.jupiter.api.Test

class StaticCellScalarizationPassTest {

  private var zeroInitialized = false

  @BeforeEach
  fun setUp() {
    zeroInitialized = DereferenceToArrayPass.zeroInitialized
    DereferenceToArrayPass.zeroInitialized = true
  }

  @AfterEach
  fun tearDown() {
    DereferenceToArrayPass.zeroInitialized = zeroInitialized
  }

  private fun scalarize(model: XcfaBuilder.() -> Unit): XcfaProcedureBuilder {
    val xcfa = XcfaBuilder("test").apply(model)
    val main = xcfa.getProcedures().first { it.name == "main" }
    StaticCellScalarizationPass().run(main)
    return main
  }

  private fun XcfaProcedureBuilder.assignments(): List<AssignStmt<*>> =
    getEdges()
      .flatMap { it.getFlatLabels() }
      .mapNotNull { (it as? StmtLabel)?.stmt as? AssignStmt<*> }

  @Test
  fun `an access to a literal address becomes its cell variable`() {
    val main = scalarize {
      procedure("main") {
          "x" type Int()
          (init to "L") { "(deref 1 0 Int)" memassign "7" }
          ("L" to final) { "x" assign "(deref 1 0 Int)" }
        }
        .start()
    }
    assertTrue(main.getEdges().all { it.label.dereferences.isEmpty() })
    val read = main.assignments().first { it.varDecl.name == "x" }.expr
    val cell = main.assignments().first { it.expr == Int(7) }.varDecl
    assertTrue(cell.name.startsWith("__cell0_"))
    assertEquals(cell.ref, read)
  }

  @Test
  fun `an access to base 0 gets a cell, as in the flat memory model`() {
    val main = scalarize {
      procedure("main") {
          "x" type Int()
          (init to "L") { "(deref 0 5 Int)" memassign "7" }
          ("L" to final) { "x" assign "(deref 0 5 Int)" }
        }
        .start()
    }
    val read = main.assignments().first { it.varDecl.name == "x" }.expr
    val cell = main.assignments().first { it.expr == Int(7) }.varDecl
    assertEquals(cell.ref, read)
  }

  @Test
  fun `an access to one of several cells becomes a case split`() {
    val main = scalarize {
      global { "i" type Int() init "0" }
      val thr = procedure("thr") { (init to final) { "i" assign "1" } }
      procedure("main") {
          "t" type Int()
          "x" type Int()
          (init to "L") { "t".start(thr) }
          ("L" to "M") { "(deref 1 i Int)" memassign "7" }
          ("M" to final) { "x" assign "(deref 1 i Int)" }
        }
        .start()
    }
    assertTrue(main.getEdges().all { it.label.dereferences.isEmpty() })
    val read = main.assignments().first { it.varDecl.name == "x" }.expr
    assertTrue(read is IteExpr<*>)
  }

  @Test
  fun `two reads that may hit no cell get independent values`() {
    val main = scalarize {
      procedure("main") {
          "p" type Int()
          "q" type Int()
          (init to "L") { assume("(= (deref p 0 Int) (deref q 0 Int))") }
          ("L" to final) {
            "p" assign "1"
            "q" assign "1"
          }
        }
        .start()
    }
    val havoced =
      main
        .getEdges()
        .flatMap { it.getFlatLabels() }
        .mapNotNull { ((it as? StmtLabel)?.stmt as? HavocStmt<*>)?.varDecl }
    assertEquals(2, havoced.toSet().size)
  }

  @Test
  fun `a partition accessed outside a rewritable statement stays in memory`() {
    val main = scalarize {
      procedure("f") {
        ("p" type Int()).direction(ParamDirection.IN)
        (init to final) { assume("true") }
      }
      procedure("main") {
          "x" type Int()
          (init to "L") { "(deref 1 0 Int)" memassign "7" }
          ("L" to final) { "f"("(deref 1 0 Int)") }
        }
        .start()
    }
    assertTrue(main.getEdges().any { it.label.dereferences.isNotEmpty() })
    assertTrue(main.assignments().none { it.varDecl.name.startsWith("__cell") })
  }
}
