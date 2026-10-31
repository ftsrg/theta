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
import hu.bme.mit.theta.xcfa.model.XcfaProcedure
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.DisplayName
import org.junit.jupiter.api.Test

/**
 * `&&` and `||` evaluate their right-hand operand only if the left one lets them.
 *
 * Both halves of that matter, and they pull against each other:
 * - an operand that *does* something -- a call -- must not run when the short-circuit skips it
 *   (`x > INT_MIN && abs(x) < k`), so its statements go behind a guard;
 * - an operand that does nothing must **not** get a guard, because the guard costs a branch.
 *
 * The second is easy to get wrong: a statement lands in `preStatements` for reasons that have
 * nothing to do with side effects -- *every parenthesised sub-expression* lifts one -- so taking
 * "the list grew" as the signal guards pure operands too. `(a && b) || (c && d)` is the whole of
 * SV-COMP's `assume_abort_if_not`, and guarding it split each such condition into two paths whose
 * arms were identical: a pure path explosion that timed out a mass of tasks which had solved in
 * seconds.
 *
 * So a parenthesised *call* must still be guarded, while a parenthesised *comparison* must not be.
 */
class ShortCircuitTest {

  private fun locationCount(body: String): Int = main(body).locs.size

  /** How many values were taken into a temporary to shield them from a later operand's effect. */
  private fun snapshotCount(body: String): Int =
    main(body).vars.count { it.name.contains("shortcircuit") }

  private fun main(body: String): XcfaProcedure {
    val parseContext = ParseContext()
    parseContext.architecture = ArchitectureType.ILP32
    val (xcfa, _, _) =
      getXcfaFromC(
        """
        extern int __VERIFIER_nondet_int(void);
        int g = 0;
        int bump(void) { g = 1; return 1; }
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
        XcfaProperty(ErrorDetection.ERROR_LOCATION),
        NullLogger.getInstance(),
      )
    return xcfa.procedures.first { it.name == "main" }
  }

  @Test
  @DisplayName("parentheses around a pure operand add no branch")
  fun parenthesesAddNoBranch() {
    // The same condition, written with and without parentheses, is the same program: the parens
    // lift a statement, but it does nothing, so it must not be pushed behind a guard.
    assertEquals(
      locationCount("if (a >= 1 && a <= 2) { g = 2; }"),
      locationCount("if ((a >= 1) && (a <= 2)) { g = 2; }"),
      "parenthesising the operands of && must not change the model",
    )
    // The shape SV-COMP writes everywhere.
    assertEquals(
      locationCount("if (a >= 1 && a <= 2 || a >= 5 && a <= 6) { g = 2; }"),
      locationCount("if ((a >= 1 && a <= 2) || (a >= 5 && a <= 6)) { g = 2; }"),
      "parenthesising the operands of || must not change the model",
    )
  }

  @Test
  @DisplayName("a call in a later operand is put behind the short-circuit")
  fun callIsGuarded() {
    // `bump()` may not run when `a != 0` is false, so its statements have to be guarded -- which
    // costs locations. Without the guard the model would be as flat as the pure one.
    val pure = locationCount("if (a != 0 && a != 1) { g = 2; }")
    val call = locationCount("if (a != 0 && bump()) { g = 2; }")
    assertTrue(
      call > pure,
      "a call in the right operand of && must be guarded by the left one (got $call locs, same as pure $pure)",
    )
    // ...and it stays guarded when it is parenthesised, which is where the guard used to be lost.
    val parenCall = locationCount("if ((a != 0) && (bump())) { g = 2; }")
    assertTrue(
      parenCall > pure,
      "a parenthesised call must still be guarded (got $parenCall locs, same as pure $pure)",
    )
  }

  @Test
  @DisplayName("a later operand's effect on what an earlier operand read is preceded by a snapshot")
  fun earlierOperandsAreSnapshotted() {
    // The operator's value is built after every operand ran, so `a > 1` would be re-read after the
    // decrement, and `g == 0` after `bump()` set `g`.
    assertTrue(snapshotCount("if (a > 1 && --a) { g = 2; }") > 0, "a > 1 must be snapshotted")
    assertTrue(snapshotCount("if (g == 0 && bump()) { g = 2; }") > 0, "g == 0 must be snapshotted")
  }

  @Test
  @DisplayName("an effect that cannot change the earlier operands adds no snapshot")
  fun noNeedlessSnapshot() {
    // A nondet call writes nothing the earlier operand reads, a call result is written only by its
    // own call, and `c` is not read before it is assigned.
    assertEquals(0, snapshotCount("if (a != 0 && __VERIFIER_nondet_int()) { g = 2; }"))
    assertEquals(0, snapshotCount("if (bump() || bump()) { g = 2; }"))
    assertEquals(0, snapshotCount("int c = 0; if (a != 0 && (c = 3)) { g = 2; }"))
  }
}
