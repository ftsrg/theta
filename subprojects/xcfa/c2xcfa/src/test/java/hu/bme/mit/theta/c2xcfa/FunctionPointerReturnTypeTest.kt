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
import hu.bme.mit.theta.xcfa.model.XCFA
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

/**
 * A call through a function pointer must build whatever the pointed-to function returns.
 *
 * The pointer carries no signature the frontend can use, so it types the call's result an `int` and
 * lets the dispatch pass pick the callee by arity. The callee may then return something else
 * entirely -- `void` above all, which is the ordinary case for a callback. Inlining that call
 * writes the callee's result into the caller's variable, and it used to build that assignment at
 * the *callee's* type: a 32-bit variable asked to be cast to the 1-bit one standing in for `void`,
 * which threw `ClassCastException` and lost the whole program. (Juliet's `_44`/`_65` variants --
 * "data flow through a function pointer" -- are exactly this, and every one of them was failing.)
 */
class FunctionPointerReturnTypeTest {

  private fun build(src: String, arithmetic: ArithmeticType): Pair<XCFA, ParseContext> {
    val parseContext = ParseContext()
    parseContext.architecture = ArchitectureType.LP64
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

  private fun buildBoth(src: String) {
    build(src, ArithmeticType.bitvector)
    build(src, ArithmeticType.integer)
  }

  @Test
  fun `a call through a pointer to a void function builds`() {
    buildBoth(
      """
      extern int __VERIFIER_nondet_int();
      static void sink(int data) { int r = data + 1; }
      int main() {
        void (*fp)(int) = sink;
        fp(__VERIFIER_nondet_int());
        return 0;
      }
      """
        .trimIndent()
    )
  }

  @Test
  fun `a call through a pointer to a narrower-returning function builds`() {
    // `char` is 8 bits, and the call's result is typed `int`: the two disagree just as `void` does.
    buildBoth(
      """
      extern int __VERIFIER_nondet_int();
      static char narrow(int x) { return (char) x; }
      int main() {
        char (*fp)(int) = narrow;
        char c = fp(__VERIFIER_nondet_int());
        return c;
      }
      """
        .trimIndent()
    )
  }

  @Test
  fun `a call through a pointer to an int function still builds`() {
    // The case that always worked -- it must keep working.
    buildBoth(
      """
      extern int __VERIFIER_nondet_int();
      static int add(int x) { return x + 1; }
      int main() {
        int (*fp)(int) = add;
        return fp(__VERIFIER_nondet_int());
      }
      """
        .trimIndent()
    )
  }

  @Test
  fun `a prototyped function's address is initialised`() {
    // A function is normally *declared* before it is defined. The variable standing for its address
    // belongs to that prototype, and the definition used to be left with no variable at all -- so
    // the address was never initialised, the pointer held an arbitrary value, and every candidate's
    // dispatch guard became satisfiable. A call through the pointer could then land in any function
    // of the right arity, which is how a program got a counterexample through a callee it can never
    // reach. The id must be a global with an initial value, one per address-taken function.
    val (xcfa, _) =
      build(
        """
        void first(int x);
        void second(int x);
        int main() {
          void (*fp)(int) = second;
          void (*gp)(int) = first;
          fp(1);
          gp(2);
          return 0;
        }
        void first(int x) { int a = x; }
        void second(int x) { int b = x; }
        """
          .trimIndent(),
        ArithmeticType.bitvector,
      )

    val addressVars =
      xcfa.globalVars.filter {
        it.wrappedVar.name.substringAfterLast("::") in setOf("first", "second")
      }
    assertEquals(2, addressVars.size, "each address-taken function needs a variable holding its id")
    assertTrue(
      addressVars.all { it.initValue != null },
      "a function's address must be initialised, or the pointer holding it is nondeterministic",
    )
    assertEquals(
      2,
      addressVars.mapNotNull { it.initValue }.toSet().size,
      "the two functions must have distinct ids",
    )
  }

  @Test
  fun `a void and an int candidate of the same arity coexist`() {
    // Dispatch picks candidates by arity, so both of these are candidates for the one call site;
    // each branch must be built at its own callee's return type.
    buildBoth(
      """
      extern int __VERIFIER_nondet_int();
      static void vsink(int data) { int r = data + 1; }
      static int  isink(int data) { return data + 1; }
      int main() {
        void (*fp)(int) = vsink;
        if (__VERIFIER_nondet_int()) fp = (void (*)(int)) isink;
        fp(__VERIFIER_nondet_int());
        return 0;
      }
      """
        .trimIndent()
    )
  }
}
