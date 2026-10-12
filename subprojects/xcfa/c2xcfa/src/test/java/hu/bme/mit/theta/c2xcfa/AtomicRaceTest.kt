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
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CArray
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CPointer
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.XcfaProperty
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.DisplayName
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.CsvSource

/**
 * What `_Atomic` makes race-free -- the variable, or what it points at.
 *
 * These are the two questions the data-race check asks, and they have different answers:
 * - a race between two **variables** is excluded when the *variable's own* type is atomic;
 * - a race between two **memory locations** is excluded when the *pointee* is.
 *
 * ```
 * _Atomic int *p;   // p is an ordinary variable; p[i] is atomic and cannot be raced on
 * int * _Atomic p;  // p itself is atomic; p[i] is not, and can be
 * ```
 *
 * Answering either with the other invents a race or hides one, so both are pinned here -- at the
 * XCFA, where the checks read them: the variable's flag on [XcfaGlobalVar], and the pointee's on
 * the type the pointer carries.
 */
class AtomicRaceTest {

  private fun build(src: String): Pair<hu.bme.mit.theta.xcfa.model.XCFA, ParseContext> {
    val parseContext = ParseContext()
    parseContext.architecture = ArchitectureType.ILP32
    val (xcfa, _, _) =
      getXcfaFromC(
        src.byteInputStream(),
        parseContext,
        false,
        XcfaProperty(ErrorDetection.DATA_RACE),
        NullLogger.getInstance(),
      )
    return xcfa to parseContext
  }

  /** `<variable atomic>/<pointee atomic>` for the global `A` the program declares. */
  private fun atomicityOf(declaration: String): String {
    val (xcfa, parseContext) =
      build(
        """
        extern void *malloc(unsigned long);
        $declaration;
        int main() { A = malloc(16); return 0; }
        """
          .trimIndent()
      )
    val global = xcfa.globalVars.first { it.wrappedVar.name.substringAfterLast("::") == "A" }
    val pointee =
      when (val type = CComplexType.getType(global.wrappedVar.ref, parseContext)) {
        is CPointer -> type.embeddedType
        is CArray -> type.embeddedType
        else -> null
      }
    return "${global.atomic}/${pointee?.isAtomic == true}"
  }

  @ParameterizedTest(name = "{0} -> variable/pointee = {1}")
  @DisplayName("which level _Atomic reaches")
  @CsvSource(
    // declaration                    variable / pointee
    "int *A, false/false",
    // The pointer is ordinary; what it points at is atomic. `A[i]` cannot race, `A` can.
    "_Atomic int *A, false/true",
    "_Atomic(int) *A, false/true",
    // The pointer itself is atomic; what it points at is not. Exactly the other way round.
    "int * _Atomic A, true/false",
    "_Atomic(int *) A, true/false",
    // Both.
    "_Atomic int * _Atomic A, true/true",
  )
  fun `atomicity lands on the level it was written at`(declaration: String, expected: String) =
    assertEquals(expected, atomicityOf(declaration), "for `$declaration`")

  /** Whether the global function pointer `fp` the program declares is an atomic variable. */
  private fun funcPointerIsAtomic(declaration: String): Boolean {
    val (xcfa, _) = build("$declaration void main() { fp = 0; }")
    return xcfa.globalVars.first { it.wrappedVar.name.substringAfterLast("::") == "fp" }.atomic
  }

  @ParameterizedTest(name = "{0} -> atomic = {1}")
  @DisplayName("_Atomic on a function-pointer declarator makes the pointer atomic")
  @CsvSource(
    // The star sits inside the declarator's parentheses, so its `_Atomic` is carried by the
    // declarator (not the type specifier). It makes the pointer VARIABLE atomic -- writing `fp` is
    // race-free -- exactly as `int * _Atomic p` does. const/volatile there change nothing.
    "void (*fp)(void);, false",
    "void (* _Atomic fp)(void);, true",
    "void (* const fp)(void);, false",
  )
  fun `atomic function pointer`(declaration: String, expected: Boolean) =
    assertEquals(expected, funcPointerIsAtomic(declaration), "for `$declaration`")
}
