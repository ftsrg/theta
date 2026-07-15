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
import org.junit.jupiter.api.Test

/**
 * A signed overflow inside a short-circuited operand must still be checked.
 *
 * `OverflowDetectionPass` finds the arithmetic to range-check, but `&&`/`||` fold their operands
 * into a single condition and the pass threads each operand's short-circuit guard through as
 * `Ite(reached, arith, 0)` -- the operand overflows only when it is actually evaluated. The integer
 * encoding range-checks the whole `Ite` (0 is in range), but the *bitvector* encoding has to
 * reconstruct the overflow from the operands, which sit inside the `then` branch, and it used to see
 * only the `Ite` and give up -- silently dropping the check. `P1 & (P1 - 1)` (a power-of-two test
 * folded into a bitwise expression, so the whole program is analysed with bitvectors) then overflows
 * unreported at `P1 == INT_MIN`, and a real bug was proved Safe. This pins that the folded operand
 * still gets an overflow check.
 */
class OverflowShortCircuitTest {

  private fun overflowChecks(body: String): Int {
    val parseContext = ParseContext()
    parseContext.architecture = ArchitectureType.ILP32
    val (xcfa, _, _) =
      getXcfaFromC(
        """
        extern int __VERIFIER_nondet_int(void);
        int main(void) {
          int a = __VERIFIER_nondet_int();
          $body
          return 0;
        }
        """
          .trimIndent()
          .byteInputStream(),
        parseContext,
        false,
        XcfaProperty(ErrorDetection.OVERFLOW),
        NullLogger.getInstance(),
      )
    val main = xcfa.procedures.first { it.name == "main" }
    return main.errorLoc.map { it.incomingEdges.size }.orElse(0)
  }

  @Test
  @DisplayName("a signed subtraction folded into a bitwise condition is still overflow-checked")
  fun foldedBitwiseSubtractionIsChecked() {
    // `a - 1` sits inside `a & (a - 1)`, whose `&` makes the whole program bitvector-analysed, and
    // the `1 && (... || 0)` wrapping folds it behind a short-circuit guard. It overflows at INT_MIN,
    // so the error location must be reachable.
    assertTrue(
      overflowChecks("if ( 1 && ((((a & (a - 1)) == 0)) || 0) ) { return 1; }") > 0,
      "a signed `a - 1` folded into a bitwise short-circuit must still reach an overflow check",
    )
  }

  @Test
  @DisplayName("a bitvector overflow as its own statement is checked (the control)")
  fun bitwiseStatementIsChecked() {
    // The same `a - 1` under bitvector arithmetic, but as a plain statement rather than folded --
    // this path was never broken, and anchors that the folded case above matches it.
    assertTrue(
      overflowChecks("int m = a & 7; int b = a - 1; if (b + m > 0) { return 1; }") > 0,
      "a signed `a - 1` under bitvector arithmetic must reach an overflow check",
    )
  }
}
