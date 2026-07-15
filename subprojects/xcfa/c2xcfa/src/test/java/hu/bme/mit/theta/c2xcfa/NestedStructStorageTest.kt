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
import hu.bme.mit.theta.core.stmt.MemoryAssignStmt
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.ArchitectureType
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.model.StmtLabel
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.DisplayName
import org.junit.jupiter.api.Test

/**
 * A struct-typed *field* is an object of its own, so it is allocated storage of its own -- from the
 * allocation counter, at run time.
 *
 * A struct variable's value IS its base id and `s.f` reads `__arrays_T[s][i]`, so a field that is
 * itself a struct holds a base id in turn (`o.in.x` is `__arrays[__arrays[o][0]][0]`). Two things
 * went wrong here, and the assertion below covers both:
 * - only *declared* variables were given a base at all, leaving every inner struct's unconstrained,
 *   so the solver could pick one already in use and `struct Out o, p; o.in.x = 1; p.in.x = 2;` read
 *   `o.in.x` back as 2;
 * - the base was a compile-time constant, so every activation of the procedure reused it and two
 *   recursive frames -- or two threads running the function -- aliased.
 *
 * Both are answered by allocating each inner struct from the runtime counter, which is what is
 * checked: one counter-derived write per object into its field cell. A constant would fail the
 * counter check; no allocation at all would fail the count.
 */
class NestedStructStorageTest {

  /** Field-cell writes whose value comes from the allocation counter -- i.e. the inner allocations. */
  private fun allocatedInnerStructs(body: String): List<MemoryAssignStmt<*, *, *>> {
    val parseContext = ParseContext()
    parseContext.architecture = ArchitectureType.LP64
    val (xcfa, _, _) =
      getXcfaFromC(
        """
        extern unsigned long __VERIFIER_nondet_ulong(void);
        struct In { unsigned long x; };
        struct Out { struct In in; unsigned long y; };
        int main(void) {
          unsigned long n = __VERIFIER_nondet_ulong();
          $body
        }
        """
          .trimIndent()
          .byteInputStream(),
        parseContext,
        false,
        XcfaProperty(ErrorDetection.ERROR_LOCATION),
        NullLogger.getInstance(),
      )
    return xcfa.procedures
      .flatMap { it.edges }
      .flatMap { it.getFlatLabels() }
      .filterIsInstance<StmtLabel>()
      .map { it.stmt }
      .filterIsInstance<MemoryAssignStmt<*, *, *>>()
      .filter { stmt -> ExprUtils.getVars(stmt.expr).any { it.name == "__malloc" } }
  }

  @Test
  @DisplayName("each object's inner struct is allocated a base of its own, at run time")
  fun innerStructsAreAllocatedSeparately() {
    // Two objects, so two inner structs, so two allocations -- and each takes its base from the
    // counter, which is what keeps two activations of the enclosing procedure apart.
    val allocations =
      allocatedInnerStructs(
        "struct Out o; struct Out p;" +
          " o.in.x = n; p.in.x = n + 1;" +
          " return (int) (o.in.x + p.in.x);"
      )
    assertEquals(
      2,
      allocations.size,
      "each inner struct needs its own base, allocated from the counter (got $allocations)",
    )
  }
}
