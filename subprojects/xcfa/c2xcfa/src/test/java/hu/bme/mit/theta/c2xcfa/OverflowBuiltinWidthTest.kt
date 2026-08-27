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
 * `__builtin_uadd_overflow` overflows at *its own* width, not at the width of `res`.
 *
 * The typed forms fix their width by name -- `uadd` is `unsigned int`, `uaddl` is `unsigned long`,
 * the `ll` forms `unsigned long long` -- but a caller may legitimately hand them a wider `res`.
 * aws-c-common's `aws_add_u32_saturating` writes a 32-bit `__builtin_uadd_overflow` through an
 * `unsigned long`. Reading the width from `res` then carries the addition out in 64 bits, where two
 * 32-bit operands can never overflow, so the call always answers "no overflow" and the saturating
 * result disagrees with the caller's own `a > UINT32_MAX - b` test -- a false `unreach-call` across
 * the aws saturating suite.
 *
 * The flag is emitted as `overflow := (wrapped_sum < a)`, so the modulus the sum is wrapped at *is*
 * the width the overflow is computed at: it must be 2^32 here, not 2^64.
 */
class OverflowBuiltinWidthTest {

  private fun overflowFlagExpr(body: String): String {
    val parseContext = ParseContext()
    parseContext.architecture = ArchitectureType.LP64
    parseContext.arithmetic = ArithmeticType.integer
    val (xcfa, _, _) =
      getXcfaFromC(
        // `flag` is returned so the overflow temporary stays live -- an unused builtin result is
        // dead code and gets removed before the model is built.
        """
        extern unsigned int __VERIFIER_nondet_uint(void);
        extern unsigned long __VERIFIER_nondet_ulong(void);
        int main(void) {
          $body
          return flag;
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
      .filterIsInstance<AssignStmt<*>>()
      .filter { it.varDecl.name.contains("overflow") }
      .joinToString(" ") { it.expr.toString() }
  }

  @Test
  @DisplayName("a 32-bit add-overflow written through a 64-bit result still overflows at 32 bits")
  fun uaddOverflowUsesItsOwnWidth() {
    val flag =
      overflowFlagExpr(
        "unsigned int a = __VERIFIER_nondet_uint(); unsigned int b = __VERIFIER_nondet_uint();" +
          " unsigned long c; int flag = __builtin_uadd_overflow(a, b, &c);"
      )
    assertTrue(flag.isNotEmpty(), "the overflow flag assignment should be in the model")
    assertTrue(
      flag.contains("4294967296"),
      "`uadd` must wrap its sum at 2^32 -- the builtin's own width -- got: $flag",
    )
    assertTrue(
      !flag.contains("18446744073709551616"),
      "`uadd` must not be carried out at `res`'s 64-bit width, where it could never overflow: $flag",
    )
  }

  @Test
  @DisplayName("a 64-bit add-overflow still overflows at 64 bits")
  fun uaddlOverflowUsesItsOwnWidth() {
    // The control: `uaddl` genuinely is 64-bit, so it must keep wrapping at 2^64.
    val flag =
      overflowFlagExpr(
        "unsigned long a = __VERIFIER_nondet_ulong(); unsigned long b = __VERIFIER_nondet_ulong();" +
          " unsigned long c; int flag = __builtin_uaddl_overflow(a, b, &c);"
      )
    assertTrue(
      flag.contains("18446744073709551616"),
      "`uaddl` must wrap its sum at 2^64 -- got: $flag",
    )
  }
}
