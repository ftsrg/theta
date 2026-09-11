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

import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.MemoryAssignStmt
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test

/**
 * The pass drops a string literal's per-character initialization only when nothing can read it
 * back. Every way the address can still reach a read has to hold it back, or the program loses
 * writes it depends on.
 */
class StringLiteralInitPassTest {

  private fun runPass(input: XcfaProcedureBuilderContext.() -> Unit): XcfaProcedureBuilder =
    StringLiteralInitPass().runChecked(XcfaBuilder("").procedure("main", input).builder)

  /** Writes still aimed at a literal's cells after the pass. */
  private fun XcfaProcedureBuilder.literalInitWrites(): Int =
    getEdges()
      .flatMap { it.label.getFlatLabels() }
      .count { label ->
        val deref = ((label as? StmtLabel)?.stmt as? MemoryAssignStmt<*, *, *>)?.deref
        val base = (deref?.array as? RefExpr<*>)?.decl as? VarDecl<*>
        base?.name?.contains("__theta_str") == true
      }

  @Test
  fun unreadLiteralInitializationIsDropped() {
    val result = runPass {
      "__theta_str0" type Int()
      (init to "L1") {
        "(deref __theta_str0 0 Int)" memassign "104"
        "(deref __theta_str0 1 Int)" memassign "105"
        "(deref __theta_str0 2 Int)" memassign "0"
      }
    }
    assertEquals(0, result.literalInitWrites())
  }

  @Test
  fun aReadCellKeepsTheInitialization() {
    val result = runPass {
      "__theta_str0" type Int()
      "c" type Int()
      (init to "L1") { "(deref __theta_str0 0 Int)" memassign "104" }
      ("L1" to "L2") { "c" assign "(deref __theta_str0 0 Int)" }
    }
    assertEquals(1, result.literalInitWrites())
  }

  /**
   * Reads go through a pointer variable, never the literal itself, and the pointer may have been
   * copied more than once on the way -- so the address has to be followed to a fixpoint.
   */
  @Test
  fun aLiteralReachedThroughCopiedPointersKeepsTheInitialization() {
    val result = runPass {
      "__theta_str0" type Int()
      "s" type Int()
      "t" type Int()
      "c" type Int()
      (init to "L1") { "(deref __theta_str0 0 Int)" memassign "104" }
      ("L1" to "L2") { "s" assign "__theta_str0" }
      ("L2" to "L3") { "t" assign "s" }
      ("L3" to "L4") { "c" assign "(deref t 0 Int)" }
    }
    assertEquals(1, result.literalInitWrites())
  }

  /** Once the address is in memory it can be loaded back through a base the pass cannot name. */
  @Test
  fun aLiteralStoredIntoMemoryKeepsTheInitialization() {
    val result = runPass {
      "__theta_str0" type Int()
      "p" type Int()
      (init to "L1") { "(deref __theta_str0 0 Int)" memassign "104" }
      ("L1" to "L2") { "(deref p 0 Int)" memassign "__theta_str0" }
    }
    assertEquals(1, result.literalInitWrites())
  }

  /** A pointer copied from a literal but only ever compared is still not a read of its cells. */
  @Test
  fun aCopiedPointerThatIsNeverDereferencedIsStillDropped() {
    val result = runPass {
      "__theta_str0" type Int()
      "s" type Int()
      (init to "L1") { "(deref __theta_str0 0 Int)" memassign "104" }
      ("L1" to "L2") { "s" assign "__theta_str0" }
      ("L2" to "L3") { assume("(/= s 0)") }
    }
    assertEquals(0, result.literalInitWrites())
  }
}
