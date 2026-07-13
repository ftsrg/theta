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
package hu.bme.mit.theta.c2xcfa

import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.ArchitectureType
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.XcfaProperty
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.DisplayName
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.ValueSource

/**
 * C11 `<stdatomic.h>`.
 *
 * The types are ordinary `_Atomic` types, and are declared as such in the bundled header. The
 * *operations* are type-generic, which C expresses with macros and this grammar cannot express at
 * all -- so they are recognised by name and built directly, exactly like the `__atomic_*` builtins
 * they compile down to.
 *
 * That the program *builds* is the least of it: an atomic variable has to stay atomic (the whole
 * point of declaring it), and a read-modify-write has to yield the value that was there **before**,
 * which is the easiest thing in the world to get backwards. The semantics are checked where they
 * can be checked properly -- by running the verifier -- so what is pinned here is that every form
 * reaches the XCFA at all, and that `atomic_int` is still atomic when it gets there.
 */
class StdAtomicTest {

  private fun buildAtomicUse(statement: String) {
    val parseContext = ParseContext()
    parseContext.architecture = ArchitectureType.ILP32
    val (xcfa, _, _) =
      getXcfaFromC(
        """
        #include <stdatomic.h>
        atomic_int x;
        int main() { $statement return 0; }
        """
          .trimIndent()
          .byteInputStream(),
        parseContext,
        false,
        XcfaProperty(ErrorDetection.DATA_RACE),
        NullLogger.getInstance(),
      )
    // `atomic_int` is `_Atomic int`: the variable itself is atomic, and must still say so here --
    // this is the flag the data-race check reads, and without it two threads touching `x` would be
    // reported as racing.
    val x = xcfa.globalVars.first { it.wrappedVar.name.substringAfterLast("::") == "x" }
    assertTrue(x.atomic || x.pointsToAtomic, "atomic_int x must reach the XCFA as atomic")
  }

  @ParameterizedTest(name = "{0}")
  @DisplayName("every stdatomic operation builds, and the type stays atomic")
  @ValueSource(
    strings =
      [
        "atomic_store(&x, 7);",
        "atomic_store_explicit(&x, 7, memory_order_seq_cst);",
        "atomic_init(&x, 7);",
        "int v = atomic_load(&x);",
        "int v = atomic_load_explicit(&x, memory_order_acquire);",
        "int v = atomic_fetch_add(&x, 2);",
        "int v = atomic_fetch_add_explicit(&x, 2, memory_order_relaxed);",
        "int v = atomic_fetch_sub(&x, 2);",
        "int v = atomic_exchange(&x, 9);",
        "int v = atomic_exchange_explicit(&x, 9, memory_order_acq_rel);",
        // the plain assignment an atomic type still supports
        "x = 3;",
      ]
  )
  fun `stdatomic operations`(statement: String) = buildAtomicUse(statement)
}
