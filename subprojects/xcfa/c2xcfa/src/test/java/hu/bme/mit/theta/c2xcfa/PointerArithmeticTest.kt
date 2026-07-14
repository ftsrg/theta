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
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.ArithmeticType
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.XcfaProperty
import org.junit.jupiter.api.Test

/**
 * `p = q + i` stores no offset in a pointer value (an object id), so it used to be refused with
 * "Pointer arithmetic not supported". It is now read as `p = &q[i]` -- `ref(deref(q, i))` -- and
 * [hu.bme.mit.theta.xcfa.passes.ReferenceElimination] splits `p` into a `base` / `offset` pair that
 * gives the offset a home. This is how CIL spells every array and field access: `tmp = base + idx;
 * *tmp`.
 *
 * Building the program is the assertion: on a regression these throw (the frontend refusal, or a
 * "bare use of split variable" from the pass), so `buildBoth` reaching its end is a pass.
 */
class PointerArithmeticTest {

  private fun build(src: String, arithmetic: ArithmeticType) {
    val parseContext = ParseContext()
    parseContext.architecture = ArchitectureType.ILP32
    parseContext.arithmetic = arithmetic
    getXcfaFromC(
      src.byteInputStream(),
      parseContext,
      false,
      XcfaProperty(ErrorDetection.ERROR_LOCATION),
      NullLogger.getInstance(),
    )
  }

  private fun buildBoth(src: String) {
    build(src, ArithmeticType.bitvector)
    build(src, ArithmeticType.integer)
  }

  private fun main(body: String) = "extern void reach_error(); int main() { $body return 0; }"

  @Test
  fun `taking the address of an array element builds`() {
    buildBoth(main("int a[10]; int *p = &a[3]; *p = 5; if (a[3] != 5) reach_error();"))
  }

  @Test
  fun `a pointer plus an integer assigned to a pointer builds`() {
    buildBoth(main("int a[10]; int *p = a + 3; *p = 5; if (a[3] != 5) reach_error();"))
  }

  @Test
  fun `a pointer minus an integer builds`() {
    buildBoth(
      main("int a[10]; int *q = &a[7]; int *p = q - 4; *p = 5; if (a[3] != 5) reach_error();")
    )
  }

  @Test
  fun `chained pointer arithmetic through a reused intermediate builds`() {
    // The base of the second step is itself a split pointer, so this exercises the composing branch
    // (`p_base = q_base`, `p_offset = q_offset + i`) rather than re-addressing a bare split
    // variable.
    buildBoth(
      main(
        "int a[10]; int *q = a; int *p = q + 7; int *r = p - 4; *r = 5; if (a[3] != 5) reach_error();"
      )
    )
  }
}
