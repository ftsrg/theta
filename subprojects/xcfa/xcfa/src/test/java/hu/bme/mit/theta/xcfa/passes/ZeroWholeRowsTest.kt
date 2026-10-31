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
import hu.bme.mit.theta.core.type.arraytype.ArrayLitExpr
import hu.bme.mit.theta.core.type.arraytype.ArrayWriteExpr
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.xcfa.model.SequenceLabel
import hu.bme.mit.theta.xcfa.model.StmtLabel
import hu.bme.mit.theta.xcfa.model.XcfaBuilder
import hu.bme.mit.theta.xcfa.model.XcfaLabel
import hu.bme.mit.theta.xcfa.model.XcfaProcedureBuilderContext
import hu.bme.mit.theta.xcfa.model.procedure
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test

/** Tests that [DereferenceToArrayPass] zeroes a whole row with one store where it may. */
class ZeroWholeRowsTest {

  /** The memory stores after the pass: (zero rows, single-cell stores). */
  private fun stores(body: XcfaProcedureBuilderContext.() -> Unit): Pair<Int, Int> {
    val xcfa = XcfaBuilder("")
    val proc = xcfa.procedure("main", body).builder
    xcfa.addEntryPoint(proc, listOf())
    DereferenceToArrayPass().run(proc)
    val stores =
      proc
        .getEdges()
        .flatMap { it.label.flatten() }
        .mapNotNull { (it as? StmtLabel)?.stmt as? AssignStmt<*> }
        .filter { it.varDecl.name.startsWith("__arrays") }
        .map { it.expr as ArrayWriteExpr<*, *> }
    return stores.count { it.elem is ArrayLitExpr<*, *> } to
      stores.count { it.elem !is ArrayLitExpr<*, *> }
  }

  private fun XcfaLabel.flatten(): List<XcfaLabel> =
    if (this is SequenceLabel) labels.flatMap { it.flatten() } else listOf(this)

  @Test
  fun `default stores to one object become one row store`() {
    assertEquals(
      1 to 1,
      stores {
        (init to final) {
          "(deref 1 0 Int)" memassign "0"
          "(deref 1 1 Int)" memassign "0"
          "(deref 1 2 Int)" memassign "5"
          "(deref 1 3 Int)" memassign "0"
        }
      },
    )
  }

  @Test
  fun `a read between the stores keeps them`() {
    assertEquals(
      0 to 3,
      stores {
        "x" type Int()
        (init to final) {
          "(deref 1 0 Int)" memassign "0"
          "x".assign("(deref 4 0 Int)")
          "(deref 1 1 Int)" memassign "0"
          "(deref 1 2 Int)" memassign "0"
        }
      },
    )
  }

  @Test
  fun `a repeated offset keeps the stores`() {
    assertEquals(
      0 to 3,
      stores {
        (init to final) {
          "(deref 1 0 Int)" memassign "0"
          "(deref 1 0 Int)" memassign "7"
          "(deref 1 0 Int)" memassign "0"
        }
      },
    )
  }

  @Test
  fun `the flat base keeps the stores`() {
    assertEquals(
      0 to 2,
      stores {
        (init to final) {
          "(deref 0 65536 Int)" memassign "0"
          "(deref 0 65537 Int)" memassign "0"
        }
      },
    )
  }

  @Test
  fun `a symbolic store before the stores keeps them`() {
    assertEquals(
      0 to 3,
      stores {
        "p" type Int()
        (init to final) {
          "(deref p 0 Int)" memassign "3"
          "(deref 1 0 Int)" memassign "0"
          "(deref 1 1 Int)" memassign "0"
        }
      },
    )
  }

  @Test
  fun `accesses after the last store do not matter`() {
    assertEquals(
      1 to 1,
      stores {
        "p" type Int()
        "x" type Int()
        (init to final) {
          "(deref 1 0 Int)" memassign "0"
          "(deref 1 1 Int)" memassign "0"
          "(deref p 0 Int)" memassign "3"
          "x".assign("(deref 1 0 Int)")
        }
      },
    )
  }

  @Test
  fun `stores after the first edge are kept`() {
    assertEquals(
      0 to 2,
      stores {
        (init to "L1") { assume("true") }
        ("L1" to final) {
          "(deref 1 0 Int)" memassign "0"
          "(deref 1 1 Int)" memassign "0"
        }
      },
    )
  }
}
