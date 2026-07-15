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
import hu.bme.mit.theta.core.type.LitExpr
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
 * A struct-typed *field* is an object of its own, so it needs storage of its own.
 *
 * A struct variable's value IS its base id and `s.f` reads `__arrays_T[s][i]`, so a field that is
 * itself a struct holds a base id in turn (`o.in.x` is `__arrays[__arrays[o][0]][0]`). Only declared
 * variables were ever given a base, which left every *inner* struct's base unconstrained -- free for
 * the solver to pick, including a value already in use. `struct Out o, p; o.in.x = 1; p.in.x = 2;`
 * then read `o.in.x` back as 2, conflating two objects the program keeps apart.
 *
 * Each inner struct is seeded with a distinct literal base in the procedure's init, which is what is
 * asserted here: the fixture keeps every other value nondeterministic, so a memory write of a
 * *literal* is a base seed and nothing else.
 */
class NestedStructStorageTest {

  private fun literalBaseSeeds(body: String): List<LitExpr<*>> {
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
      .mapNotNull { it.expr as? LitExpr<*> }
  }

  @Test
  @DisplayName("the inner struct of each object gets a base of its own")
  fun innerStructsDoNotShareABase() {
    // Two objects, so two inner structs, so two seeds -- and they have to differ, or the two
    // `in`s are the same object and writing one is read back through the other.
    val seeds =
      literalBaseSeeds(
        "struct Out o; struct Out p;" +
          " o.in.x = n; p.in.x = n + 1;" +
          " return (int) (o.in.x + p.in.x);"
      )
    assertEquals(2, seeds.size, "each inner struct needs its own base to be seeded (got $seeds)")
    assertEquals(
      2,
      seeds.distinct().size,
      "the two inner structs must not be given the same base (got $seeds)",
    )
  }
}
