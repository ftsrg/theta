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
package hu.bme.mit.theta.frontend

import hu.bme.mit.theta.c.frontend.dsl.gen.CParser
import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.frontend.transformation.grammar.function.FunctionVisitor
import hu.bme.mit.theta.frontend.transformation.grammar.parseTypeAware
import hu.bme.mit.theta.frontend.transformation.grammar.type.DeclarationVisitor
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CArray
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CPointer
import org.antlr.v4.runtime.CharStreams
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.DisplayName
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.CsvSource

/**
 * *Which* thing is atomic.
 *
 * `_Atomic` is not one flag on a declaration -- it attaches to a particular level of a type, and C
 * gives you four ways to say where:
 * ```
 * _Atomic int x;          // an atomic int
 * _Atomic(int) x;         // the same, said as a specifier
 * _Atomic int *p;         // a *plain* pointer to an atomic int
 * int * _Atomic p;        // an *atomic* pointer to a plain int
 * _Atomic(int *) p;       // the same as the line above
 * _Atomic int * _Atomic p // an atomic pointer to an atomic int
 * ```
 *
 * The difference is not academic: it decides what may be raced on. An access *through* `p` touches
 * what `p` points at, so `_Atomic int *p` makes `p[i]` race-free while leaving `p` itself an
 * ordinary variable; `int * _Atomic p` is the exact opposite. Answering the question with a single
 * boolean per declaration cannot tell those apart, and getting it backwards either invents a data
 * race or hides one.
 */
class CAtomicTypeTest {

  /** The type of the global `x` declared by [program], as the frontend builds it. */
  private fun typeOf(program: String): CComplexType {
    val parseContext = ParseContext()
    val logger = NullLogger.getInstance()
    val declarationVisitor =
      DeclarationVisitor(parseContext, FunctionVisitor(parseContext, logger), logger)
    val unit = parseTypeAware(CharStreams.fromString(program))
    unit.accept(declarationVisitor.typedefVisitor)

    var found: CComplexType? = null
    for (external in unit.translationUnit().externalDeclaration()) {
      val declaration = (external as? CParser.GlobalDeclarationContext)?.declaration() ?: continue
      declarationVisitor
        .getDeclarations(
          declaration.declarationSpecifiers(),
          declaration.initDeclaratorList(),
          false,
        )
        .filter { it.name == "x" }
        .forEach { found = it.actualType }
    }
    return requireNotNull(found) { "the program must declare a global `x`" }
  }

  /**
   * The type, with an `_` marking every level that is atomic -- e.g. `CPointer<_CSignedInt>` is a
   * plain pointer to an atomic int, and `_CPointer<CSignedInt>` an atomic pointer to a plain one.
   */
  private fun describe(type: CComplexType): String {
    val mark = if (type.isAtomic) "_" else ""
    return mark +
      when (type) {
        is CPointer -> "CPointer<${describe(type.embeddedType)}>"
        is CArray -> "CArray<${describe(type.embeddedType)}>"
        else -> type.javaClass.simpleName
      }
  }

  private fun check(declaration: String, expected: String, prelude: String = "") =
    assertEquals(expected, describe(typeOf("$prelude $declaration;")), "for `$declaration`")

  @ParameterizedTest(name = "{0} is {1}")
  @DisplayName("nothing is atomic unless it says so")
  @CsvSource(
    "int x, CSignedInt",
    "int *x, CPointer<CSignedInt>",
    "int **x, CPointer<CPointer<CSignedInt>>",
  )
  fun `no atomic`(declaration: String, expected: String) = check(declaration, expected)

  @ParameterizedTest(name = "{0} is {1}")
  @DisplayName("the qualifier form: _Atomic applies to the base type")
  @CsvSource(
    "_Atomic int x, _CSignedInt",
    "int _Atomic x, _CSignedInt", // a qualifier may follow the type
    "_Atomic unsigned long x, _CUnsignedLong",
    // The pointer is plain; what it points at is atomic. `p[i]` cannot race, `p` can.
    "_Atomic int *x, CPointer<_CSignedInt>",
    "_Atomic int **x, CPointer<CPointer<_CSignedInt>>",
  )
  fun `qualifier form`(declaration: String, expected: String) = check(declaration, expected)

  @ParameterizedTest(name = "{0} is {1}")
  @DisplayName("the specifier form: _Atomic(T)")
  @CsvSource(
    "_Atomic(int) x, _CSignedInt",
    "_Atomic(unsigned long) x, _CUnsignedLong",
    // The whole of `int *` is atomic: the *pointer* is, not what it points at.
    "_Atomic(int *) x, _CPointer<CSignedInt>",
    "_Atomic(int) *x, CPointer<_CSignedInt>", // pointer to an atomic int
  )
  fun `specifier form`(declaration: String, expected: String) = check(declaration, expected)

  @ParameterizedTest(name = "{0} is {1}")
  @DisplayName("after the star: an atomic pointer to a plain thing")
  @CsvSource(
    "int * _Atomic x, _CPointer<CSignedInt>",
    "int ** _Atomic x, _CPointer<CPointer<CSignedInt>>", // only the outer pointer is atomic
    "int * _Atomic * x, CPointer<_CPointer<CSignedInt>>", // only the inner one is
  )
  fun `atomic pointer`(declaration: String, expected: String) = check(declaration, expected)

  @ParameterizedTest(name = "{0} is {1}")
  @DisplayName("both at once")
  @CsvSource(
    "_Atomic int * _Atomic x, _CPointer<_CSignedInt>",
    "_Atomic(int *) * x, CPointer<_CPointer<CSignedInt>>",
  )
  fun `both`(declaration: String, expected: String) = check(declaration, expected)

  @ParameterizedTest(name = "{0} is {1}")
  @DisplayName("through a typedef")
  @CsvSource(
    "atomic_int x, _CSignedInt",
    "atomic_int *x, CPointer<_CSignedInt>",
    "int_ptr _Atomic x, _CPointer<CSignedInt>", // an atomic variable of a pointer typedef
  )
  fun `typedefs`(declaration: String, expected: String) =
    check(declaration, expected, prelude = "typedef _Atomic int atomic_int; typedef int *int_ptr;")

  @ParameterizedTest(name = "{0} is {1}")
  @DisplayName("other qualifiers alongside, in any order")
  @CsvSource(
    "const _Atomic int x, _CSignedInt",
    "_Atomic const int x, _CSignedInt",
    "volatile _Atomic int *x, CPointer<_CSignedInt>",
    "int * const _Atomic x, _CPointer<CSignedInt>",
    "int * _Atomic const x, _CPointer<CSignedInt>",
  )
  fun `mixed qualifiers`(declaration: String, expected: String) = check(declaration, expected)
}
