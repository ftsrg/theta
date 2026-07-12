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
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CArray
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CPointer
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.model.XCFA
import org.junit.jupiter.api.Assertions.assertFalse
import org.junit.jupiter.api.Assertions.assertNotNull
import org.junit.jupiter.api.Test

/**
 * Indexing an array must not change what the *index* is.
 *
 * A C type is recorded per expression, in a map keyed by the expression itself. A cast between two
 * types of equal width and signedness is a no-op, so the cast visitor hands back the very
 * expression it was given -- and `castTo` then records the target type on it. When the two are the
 * same variable, that rewrites the variable's own type everywhere it occurs.
 *
 * `a[j]` used to cast the index to the *array's* type (a pointer-wide unsigned integer, so a no-op
 * for a `size_t`-ish index), which recorded `j` itself as an array. Every later `j++` was then read
 * as pointer arithmetic and the whole program refused with "Pointer arithmetic not supported" --
 * `for (j = 0; j < n; j++) a[j] = ...`, the most ordinary loop in C.
 *
 * Building the program at all is therefore the assertion: on a regression these throw.
 */
class ArrayIndexTypeTest {

  /** Builds [src] exactly as the pipeline does, with the types it recorded along the way. */
  private fun build(src: String, arithmetic: ArithmeticType): Pair<XCFA, ParseContext> {
    val parseContext = ParseContext()
    parseContext.architecture = ArchitectureType.ILP32
    parseContext.arithmetic = arithmetic
    val (xcfa, _, _) =
      getXcfaFromC(
        src.byteInputStream(),
        parseContext,
        false,
        XcfaProperty(ErrorDetection.ERROR_LOCATION),
        NullLogger.getInstance(),
      )
    return xcfa to parseContext
  }

  /**
   * Both arithmetics, because the bug was invisible under integer arithmetic: there the conversion
   * always builds a new expression, so it has nothing to alias. Only bitvectors -- where ILP32
   * makes `unsigned int` exactly as wide and as unsigned as a pointer -- made the cast a no-op.
   */
  private fun buildBoth(src: String) {
    build(src, ArithmeticType.bitvector)
    build(src, ArithmeticType.integer)
  }

  @Test
  fun `an unsigned index may still be incremented after indexing`() {
    buildBoth(
      """
      int main() {
        int a[4];
        unsigned int j = 0;
        a[j] = 1;
        j++;
        return a[0];
      }
      """
        .trimIndent()
    )
  }

  @Test
  fun `the ordinary counting loop over an array builds`() {
    buildBoth(
      """
      extern int __VERIFIER_nondet_int();
      int main() {
        int a[4];
        unsigned int j;
        for (j = 0; j < 4; j++) {
          a[j] = __VERIFIER_nondet_int();
        }
        return a[0];
      }
      """
        .trimIndent()
    )
  }

  @Test
  fun `the same loop over a variable-length array builds`() {
    buildBoth(
      """
      extern int __VERIFIER_nondet_int();
      int main() {
        unsigned int n = 1;
        int a[n];
        unsigned int j;
        for (j = 0; j < n; j++) {
          a[j] = __VERIFIER_nondet_int();
        }
        return a[0];
      }
      """
        .trimIndent()
    )
  }

  @Test
  fun `the index keeps its own type after being used as an index`() {
    // Building is only half the story: check the index itself. It is nondeterministic here so that
    // it survives to the built XCFA -- a constant one is folded away, and a variable that is not
    // there cannot be examined.
    val (xcfa, parseContext) =
      build(
        """
        extern unsigned int __VERIFIER_nondet_uint();
        int main() {
          int a[4];
          unsigned int j = __VERIFIER_nondet_uint();
          a[j] = 1;
          j++;
          return j;
        }
        """
          .trimIndent(),
        ArithmeticType.bitvector,
      )

    val index =
      xcfa.procedures.flatMap { it.vars }.firstOrNull { it.name.substringAfterLast("::") == "j" }
    assertNotNull(index, "the index variable `j` must survive to the XCFA")

    val recorded = CComplexType.getType(index!!.ref, parseContext)
    assertFalse(
      recorded is CArray || recorded is CPointer,
      "`j` is an integer; indexing with it must not record it as $recorded",
    )
  }
}
