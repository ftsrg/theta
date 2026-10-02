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

import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.xcfa.model.VarContext
import hu.bme.mit.theta.xcfa.model.XcfaBuilder
import hu.bme.mit.theta.xcfa.model.XcfaProcedureBuilderContext
import hu.bme.mit.theta.xcfa.model.global
import hu.bme.mit.theta.xcfa.model.procedure
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test

/** Tests the memory split of [DereferenceToArrayPass] by the values base variables can hold. */
class MemoryPartitionTest {

  /** Runs the pass and returns the names of the memory arrays it created. */
  private fun arrays(
    global: VarContext.() -> Unit = {},
    body: XcfaProcedureBuilderContext.() -> Unit,
  ): Set<String> {
    val xcfa = XcfaBuilder("").also { it.global(global) }
    val proc = xcfa.procedure("main", body).builder
    xcfa.addEntryPoint(proc, listOf())
    DereferenceToArrayPass().run(proc)
    return xcfa.getVars().map { it.wrappedVar.name }.filter { it.startsWith("__arrays") }.toSet()
  }

  private val single = setOf("__arrays_Int_Int_Int")
  private val split = setOf("__arrays_Int_Int_Int_p0", "__arrays_Int_Int_Int_p1")

  @Test
  fun `distinct literal bases are split`() {
    assertEquals(
      split,
      arrays {
        (init to "L1") { "(deref 1 0 Int)" memassign "1" }
        ("L1" to final) { "(deref 2 0 Int)" memassign "2" }
      },
    )
  }

  @Test
  fun `a variable and the literal it holds share an array`() {
    assertEquals(
      single,
      arrays(global = { "p" type Int() init "1" }) {
        (init to "L1") { "(deref p 0 Int)" memassign "1" }
        ("L1" to final) { assume("(= (deref 1 0 Int) 1)") }
      },
    )
  }

  @Test
  fun `an assigned variable joins the objects it is assigned`() {
    assertEquals(
      split,
      arrays {
        "p" type Int()
        (init to "L1") { "p".assign("(ite true 1 2)") }
        ("L1" to "L2") { "(deref p 0 Int)" memassign "1" }
        ("L2" to "L3") { "(deref 1 0 Int)" memassign "1" }
        ("L3" to final) { "(deref 3 0 Int)" memassign "3" }
      },
    )
  }

  @Test
  fun `a havoced base disables the split`() {
    assertEquals(
      single,
      arrays {
        "p" type Int()
        (init to "L1") { havoc("p") }
        ("L1" to "L2") { "(deref p 0 Int)" memassign "1" }
        ("L2" to final) { "(deref 2 0 Int)" memassign "2" }
      },
    )
  }

  @Test
  fun `a possibly uninitialized base disables the split`() {
    assertEquals(
      single,
      arrays {
        "p" type Int()
        (init to "L1") { assume("true") }
        (init to "L2") { "p".assign("1") }
        ("L1" to "L2") { assume("true") }
        ("L2" to "L3") { "(deref p 0 Int)" memassign "1" }
        ("L3" to final) { "(deref 2 0 Int)" memassign "2" }
      },
    )
  }

  @Test
  fun `an uninitialized read in one branch of a choice disables the split`() {
    assertEquals(
      single,
      arrays {
        "p" type Int()
        (init to "L1") {
          nondet {
            "p".assign("1")
            "(deref p 0 Int)" memassign "1"
          }
        }
        ("L1" to final) { "(deref 2 0 Int)" memassign "2" }
      },
    )
  }

  @Test
  fun `a global assigned before its use is split`() {
    assertEquals(
      split,
      arrays(global = { "p" type Int() init "1" }) {
        (init to "L1") { "p".assign("1") }
        ("L1" to "L2") { "(deref p 0 Int)" memassign "1" }
        ("L2" to final) { "(deref 2 0 Int)" memassign "2" }
      },
    )
  }

  @Test
  fun `a global read before the init procedure assigns it disables the split`() {
    assertEquals(
      single,
      arrays(global = { "p" type Int() init "1" }) {
        (init to "L1") { "(deref p 0 Int)" memassign "1" }
        ("L1" to "L2") { "p".assign("1") }
        ("L2" to final) { "(deref 2 0 Int)" memassign "2" }
      },
    )
  }

  @Test
  fun `a base loaded from memory disables the split`() {
    assertEquals(
      single,
      arrays {
        "p" type Int()
        (init to "L1") { "(deref 1 0 Int)" memassign "2" }
        ("L1" to "L2") { "p".assign("(deref 1 0 Int)") }
        ("L2" to "L3") { "(deref p 0 Int)" memassign "1" }
        ("L3" to final) { "(deref 3 0 Int)" memassign "3" }
      },
    )
  }

  @Test
  fun `an arithmetic base disables the split`() {
    assertEquals(
      single,
      arrays {
        "p" type Int()
        (init to "L1") { "p".assign("1") }
        ("L1" to "L2") { "(deref (+ p 1) 0 Int)" memassign "1" }
        ("L2" to final) { "(deref 2 0 Int)" memassign "2" }
      },
    )
  }
}
