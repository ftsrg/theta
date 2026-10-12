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
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.DisplayName
import org.junit.jupiter.api.Test

/**
 * The two arms of an `if` are separate scopes, so a name declared in both is two variables.
 *
 * A brace-enclosed arm does not open a scope of its own (`visitBlockItemList` only does that for a
 * block nested directly inside another block), so both arms used to share the single `if` scope.
 * The second declaration then found the first in that scope's map, reused its `VarDecl`, and
 * overwrote the recorded `cType` -- leaving one variable whose C type is whichever arm was visited
 * last, used by *both*. For `if (c) { uint64_t a; } else { uint32_t a; }` -- how aws-c-common
 * writes its 64/32 bit harness pairs -- that narrows the 64-bit arm to 32 bits, which is unsound in
 * both directions: a 64-bit value silently stops being able to exceed 2^32 (hiding real bugs), and
 * the arithmetic the other arm asserts about breaks (a false alarm).
 */
class BranchScopeTest {

  private fun localsNamed(local: String, body: String): List<String> {
    val parseContext = ParseContext()
    parseContext.architecture = ArchitectureType.LP64
    val (xcfa, _, _) =
      getXcfaFromC(
        """
        extern unsigned int __VERIFIER_nondet_uint(void);
        extern unsigned long __VERIFIER_nondet_ulong(void);
        extern int __VERIFIER_nondet_bool(void);
        int main(void) {
          unsigned long g = 0;
          $body
          return (int) g;
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
      .flatMap { it.vars }
      .map { it.name }
      .filter { it.substringAfterLast("::") == local }
      .distinct()
  }

  @Test
  @DisplayName("a name declared in both arms of an if is two distinct variables")
  fun bothArmsDeclareTheSameName() {
    val names =
      localsNamed(
        "a",
        "if (__VERIFIER_nondet_bool()) { unsigned long a = __VERIFIER_nondet_ulong(); g = a; }" +
          " else { unsigned int a = __VERIFIER_nondet_uint(); g = a; }",
      )
    assertEquals(
      2,
      names.size,
      "the two arms declare different variables, so they must not share one name (got $names)",
    )
  }

  @Test
  @DisplayName("a name declared in only one arm stays a single variable")
  fun oneArmDeclaresTheName() {
    // The control: nothing collides here, so the fix must not invent a second variable.
    val names =
      localsNamed(
        "a",
        "if (__VERIFIER_nondet_bool()) { unsigned long a = __VERIFIER_nondet_ulong(); g = a; }",
      )
    assertEquals(1, names.size, "a single declaration must stay a single variable (got $names)")
  }
}
