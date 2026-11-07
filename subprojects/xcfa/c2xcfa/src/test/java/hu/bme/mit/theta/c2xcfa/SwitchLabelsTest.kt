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
import hu.bme.mit.theta.frontend.UnsupportedFrontendElementException
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.model.XCFA
import org.junit.jupiter.api.Assertions.assertThrows
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

class SwitchLabelsTest {

  private fun build(source: String): XCFA =
    getXcfaFromC(
        source.trimIndent().byteInputStream(),
        ParseContext(),
        false,
        XcfaProperty(ErrorDetection.ERROR_LOCATION),
        NullLogger.getInstance(),
      )
      .first

  private fun guards(xcfa: XCFA): String =
    xcfa.procedures.flatMap { it.edges }.joinToString("\n") { it.label.toString() }

  @Test
  fun noMatchingLabelSkipsTheBody() {
    val xcfa =
      build(
        """
        int main() {
          int r = 0;
          switch (r) {
            case 1: r = 2;
          }
          return r;
        }
        """
      )
    val main = xcfa.procedures.first { it.name == "main" }
    assertTrue(main.finalLoc.get().incomingEdges.isNotEmpty(), "the end of main became unreachable")
  }

  @Test
  fun emptyBodyIsSkipped() {
    val xcfa = build("int main() { int r = 0; switch (r) { } return r; }")
    val main = xcfa.procedures.first { it.name == "main" }
    assertTrue(main.finalLoc.get().incomingEdges.isNotEmpty(), "the end of main became unreachable")
  }

  @Test
  fun everyStackedLabelGetsAGuard() {
    val xcfa =
      build(
        """
        extern int __VERIFIER_nondet_int();
        int main() {
          int r = __VERIFIER_nondet_int();
          switch (r) {
            case 1:
            case 2: r = 12; break;
            default: r = 99;
          }
          return r;
        }
        """
      )
    val guards = guards(xcfa)
    assertTrue("(assume (= main::r 2))" in guards, guards)
    assertTrue("(not (= main::r 2))" in guards, guards)
  }

  @Test
  fun labelInsideABodyStatementIsRefused() {
    assertThrows(UnsupportedFrontendElementException::class.java) {
      build(
        """
        extern int __VERIFIER_nondet_int();
        int main() {
          int r = __VERIFIER_nondet_int();
          switch (r) {
            case 1: { r = 1; case 2: r = 2; }
          }
          return r;
        }
        """
      )
    }
  }
}
