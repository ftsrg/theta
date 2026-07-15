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
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.ArchitectureType
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.ArithmeticType
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.model.StmtLabel
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.DisplayName
import org.junit.jupiter.api.Test

/**
 * A pointer parameter that is incremented (`s++`) gets split by
 * [hu.bme.mit.theta.xcfa.passes.ReferenceElimination] into a `base`/`offset` pair. That pass runs
 * per-procedure, *before* inlining, so it never sees the call binding `s = arg`. If it splits the
 * parameter without seeding the halves, `s_base`/`s_offset` enter the procedure unconstrained -- the
 * solver then picks an out-of-range offset and walks off the object, a false `valid-deref` on every
 * `str*`-style callee (the whole array-memsafety/termination `alloca` string cluster).
 *
 * The fix seeds the halves at the entry from the still-bound parameter (`s_base = s`, `s_offset =
 * 0`). Since the offset is only ever otherwise assigned `offset + 1` (the increment), an assignment
 * of a *literal* to a split `_offset` variable is exactly the seed: its presence is the assertion.
 */
class PointerParameterTest {

  private fun offsetSeededFor(arithmetic: ArithmeticType): Boolean {
    val parseContext = ParseContext()
    parseContext.architecture = ArchitectureType.ILP32
    parseContext.arithmetic = arithmetic
    val (xcfa, _, _) =
      getXcfaFromC(
        // `f`'s parameter is incremented, so it is split; `main` passes a bare array, whose walk is
        // in bounds (the null terminator sits at index 0), so nothing here should reach an offset
        // that is not seeded from the argument.
        """
        int f(const char *s) { while (*s != '\0') { s++; } return *s; }
        int main(void) { char a[4]; a[0] = '\0'; return f(a); }
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
      .filterIsInstance<AssignStmt<*>>()
      .any { it.varDecl.name.endsWith("_offset") && it.expr is LitExpr<*> }
  }

  @Test
  @DisplayName("a split pointer parameter is seeded from its argument (bitvector)")
  fun splitParameterSeededBitvector() {
    assertTrue(
      offsetSeededFor(ArithmeticType.bitvector),
      "a split pointer parameter's offset must be seeded (to 0) from the bound argument, " +
        "or it enters the callee unconstrained and false-alarms valid-deref",
    )
  }

  @Test
  @DisplayName("a split pointer parameter is seeded from its argument (integer)")
  fun splitParameterSeededInteger() {
    assertTrue(
      offsetSeededFor(ArithmeticType.integer),
      "a split pointer parameter's offset must be seeded (to 0) from the bound argument",
    )
  }
}
