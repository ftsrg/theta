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
import org.junit.jupiter.api.Assertions.assertNotEquals
import org.junit.jupiter.api.Assertions.assertNotNull
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

/**
 * A function that is only *declared* here can still have its address taken.
 *
 * Only functions **defined** in this translation unit used to get a variable standing for their
 * address, so `p = malloc` -- as opposed to `malloc(n)` -- resolved to nothing and died with "No
 * such variable or macro: malloc". Calling one always worked, because a call is resolved by name
 * much later; it is using one as a *value* that had nowhere to point. It is not a rare shape:
 * preprocessed sources hand a whole table of library functions to an allocator struct, and the
 * initializer is evaluated at the position of the object's *tentative* declaration -- before the
 * prototype it names -- so even a plainly ordered file hits it.
 */
class UndefinedFunctionAddressTest {

  private fun build(src: String, arithmetic: ArithmeticType): XCFA {
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
    return xcfa
  }

  private fun buildBoth(src: String) {
    build(src, ArithmeticType.bitvector)
    build(src, ArithmeticType.integer)
  }

  @Test
  fun `an undefined function's address survives a reordered initializer`() {
    // Verbatim the shape of goblint-coreutils' `stdlib_allocator`. The tentative declaration fixes
    // the position at which the later initializer is evaluated, so `&malloc` is reached *before*
    // the prototype that declares it.
    buildBoth(
      """
      struct allocator { void *(*alloc)(unsigned long); };
      struct allocator stdlib_allocator;
      extern void *malloc(unsigned long size);
      extern void *malloc(unsigned long size);
      struct allocator stdlib_allocator = {(void *(*)(unsigned long))(& malloc)};
      int main() {
        void *(*f)(unsigned long) = malloc;
        return f == stdlib_allocator.alloc ? 0 : 1;
      }
      """
        .trimIndent()
    )
  }

  @Test
  fun `a function used before its own prototype resolves`() {
    // The other half of the same reordering: the *use* sits in a function body that is visited
    // before the declaration is reached. This is how every LDV `.cil.i` writes
    // `__VERIFIER_nondet_int`.
    buildBoth(
      """
      int wrapper(void) { return __VERIFIER_nondet_int(); }
      extern int __VERIFIER_nondet_int(void);
      int main() { return wrapper(); }
      """
        .trimIndent()
    )
  }

  @Test
  fun `an undefined function declared twice gets one id`() {
    // Two declarations must not mint two variables: `fp != gp` below would then be satisfiable even
    // though both hold the same function.
    val xcfa =
      build(
        """
        int libf(int x);
        int libf(int x);
        int defined(int x) { return x + 1; }
        int main() {
          int (*fp)(int) = libf;
          int (*gp)(int) = libf;
          int (*hp)(int) = defined;
          if (fp != gp) return 1;
          return fp(1) + hp(2);
        }
        """
          .trimIndent(),
        ArithmeticType.bitvector,
      )

    fun varsNamed(name: String) =
      xcfa.globalVars.filter { it.wrappedVar.name.substringAfterLast("::") == name }

    val undefined = varsNamed("libf")
    assertEquals(
      1,
      undefined.size,
      "a function declared twice must get one variable, or two references to it compare unequal",
    )
    assertNotNull(
      undefined.single().initValue,
      "an undefined function's address must be initialised too, or a pointer holding it satisfies" +
        " another candidate's dispatch guard and the call lands in the wrong function",
    )
    val defined = varsNamed("defined")
    assertEquals(1, defined.size)
    assertNotEquals(
      undefined.single().initValue,
      defined.single().initValue,
      "distinct functions need distinct ids",
    )
    assertTrue(
      xcfa.procedures.none { it.name == "libf" },
      "an undefined function has no body, so it is never a dispatch candidate",
    )
  }

  @Test
  fun `an undefined function can still be called directly`() {
    // The whole library-call chain (CLibraryFunctionsPass / LibraryStubsPass /
    // UnresolvedInvokeToHavocPass) resolves these by name; giving them an id must not disturb it.
    buildBoth(
      """
      extern int __VERIFIER_nondet_int(void);
      extern int __VERIFIER_nondet_int(void);
      extern void *malloc(unsigned long size);
      int main() {
        int *p = (int *) malloc(sizeof(int));
        if (!p) return 0;
        *p = __VERIFIER_nondet_int();
        return *p;
      }
      """
        .trimIndent()
    )
  }
}
