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
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.CsvSource

/**
 * Automatic arithmetic selection with a solver that divides integers only by constants (Yices): a
 * `/` or `%` by anything but a literal has to switch to bitvectors.
 */
class NonConstantDivisorArithmeticTest {

  @ParameterizedTest(name = "{0} (constant divisors only: {1}) -> {2}")
  @CsvSource(
    "'r = x % n;', true, bitvector",
    "'r = x / n;', true, bitvector",
    "'r = x; r %= n;', true, bitvector",
    "'r = x; r /= n;', true, bitvector",
    "'r = x % n;', false, integer",
    "'r = x % 7;', true, integer",
    "'r = x / (8U);', true, integer",
    "'r = x; r %= 0x10;', true, integer",
    "'r = x * n;', true, integer",
  )
  fun `non-constant divisors select bitvectors only when the solver needs them`(
    statement: String,
    constantIntDivisorsOnly: Boolean,
    expected: ArithmeticType,
  ) {
    val parseContext = ParseContext()
    parseContext.architecture = ArchitectureType.ILP32
    parseContext.isConstantIntDivisorsOnly = constantIntDivisorsOnly
    getXcfaFromC(
      """
      extern int __VERIFIER_nondet_int(void);
      int main() { int x = __VERIFIER_nondet_int(); int n = __VERIFIER_nondet_int(); int r;
        $statement return r; }
      """
        .trimIndent()
        .byteInputStream(),
      parseContext,
      false,
      XcfaProperty(ErrorDetection.ERROR_LOCATION),
      NullLogger.getInstance(),
    )
    assertEquals(expected, parseContext.arithmetic)
  }
}
