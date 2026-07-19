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
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.XcfaProperty
import org.junit.jupiter.api.Assertions.assertDoesNotThrow
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

/**
 * `switch` on a wide controlling expression (e.g. `size_t`) with narrower `int` case labels used
 * to throw "(Bv 64) and (Bv 32) can not be unified" when the guard compared them directly. C
 * converts labels to the controlling expression's promoted type, so the comparison must happen in
 * the operands' common type.
 */
class SwitchWidthTest {

  @Test
  fun switchOnWideValueWithNarrowLabelsBuilds() {
    assertDoesNotThrow {
      val parseContext = ParseContext()
      val (xcfa, _, _) =
        getXcfaFromC(
          """
          extern unsigned long __VERIFIER_nondet_ulong();
          int main() {
            unsigned long v = __VERIFIER_nondet_ulong();
            int r = -1;
            switch (v) {
              case 1: r = 10; break;
              case 2: r = 20; break;
              default: r = 0;
            }
            return r;
          }
          """
            .trimIndent()
            .byteInputStream(),
          parseContext,
          false,
          XcfaProperty(ErrorDetection.ERROR_LOCATION),
          NullLogger.getInstance(),
        )
      assertTrue(xcfa.procedures.isNotEmpty(), "the program must build an XCFA")
    }
  }
}
