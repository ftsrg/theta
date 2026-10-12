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
 * What a C declaration actually declares.
 *
 * A declaration's type is assembled from the specifiers written before the declarator --
 * `unsigned`, `long`, `const`, a struct tag, a typedef name -- which arrive as a *list*, in
 * whatever order the programmer wrote them. C gives that list no significance: `unsigned long int`,
 * `long unsigned int` and `int unsigned long` are the same type, and `const T` and `T const` are
 * the same type. Anything that merges the list by *position* will therefore be wrong for some
 * spelling of some type, and it will be wrong quietly -- the declaration still parses, it just
 * means something else.
 *
 * So this pins the type, spelling by spelling.
 */
class CTypeDeclarationTest {

  /** The type of the global `x` declared by [program], as the frontend builds it. */
  private fun typeOf(program: String): CComplexType {
    val parseContext = ParseContext()
    val logger = NullLogger.getInstance()
    val declarationVisitor =
      DeclarationVisitor(parseContext, FunctionVisitor(parseContext, logger), logger)

    // The same type-aware parse the frontend uses: without it, `x` would be taken for a type name.
    val unit = parseTypeAware(CharStreams.fromString(program))
    unit.accept(declarationVisitor.typedefVisitor) // typedef names must be known first

    var found: CComplexType? = null
    for (external in unit.translationUnit().externalDeclaration()) {
      val declaration = (external as? CParser.GlobalDeclarationContext)?.declaration() ?: continue
      // Every declaration is processed, in order: a struct's tag has to be registered by the
      // declaration that defines it before a later one can refer to it.
      val declarations =
        declarationVisitor.getDeclarations(
          declaration.declarationSpecifiers(),
          declaration.initDeclaratorList(),
          false,
        )
      declarations.filter { it.name == "x" }.forEach { found = it.actualType }
    }
    return requireNotNull(found) { "the program must declare a global `x`" }
  }

  /** e.g. `CPointer<CStruct>`, `CPointer<CPointer<CSignedInt>>`. */
  private fun describe(type: CComplexType): String =
    when (type) {
      is CPointer -> "CPointer<${describe(type.embeddedType)}>"
      is CArray -> "CArray<${describe(type.embeddedType)}>"
      else -> type.javaClass.simpleName
    }

  private fun check(declaration: String, expected: String, prelude: String = "") {
    assertEquals(expected, describe(typeOf("$prelude $declaration;")), "for `$declaration`")
  }

  @ParameterizedTest(name = "{0} is {1}")
  @DisplayName("the plain integer types")
  @CsvSource(
    "int x, CSignedInt",
    "signed x, CSignedInt",
    "signed int x, CSignedInt",
    "unsigned x, CUnsignedInt",
    "unsigned int x, CUnsignedInt",
    "short x, CSignedShort",
    "short int x, CSignedShort",
    "unsigned short x, CUnsignedShort",
    "long x, CSignedLong",
    "long int x, CSignedLong",
    "unsigned long x, CUnsignedLong",
    "unsigned long int x, CUnsignedLong",
    "long long x, CSignedLongLong",
    "long long int x, CSignedLongLong",
    "unsigned long long x, CUnsignedLongLong",
    "char x, CSignedChar",
    "signed char x, CSignedChar",
    "unsigned char x, CUnsignedChar",
    "_Bool x, CBool",
    "float x, CFloat",
    "double x, CDouble",
    "long double x, CLongDouble",
  )
  fun `plain types`(declaration: String, expected: String) = check(declaration, expected)

  @ParameterizedTest(name = "{0} is {1}")
  @DisplayName("specifier order does not matter")
  @CsvSource(
    // C gives the order of specifiers no meaning at all; these all name the same type.
    "long unsigned int x, CUnsignedLong",
    "int unsigned long x, CUnsignedLong",
    "int long unsigned x, CUnsignedLong",
    "unsigned int long x, CUnsignedLong",
    "int signed x, CSignedInt",
    "int unsigned x, CUnsignedInt",
    "int short x, CSignedShort",
    "int long x, CSignedLong",
  )
  fun `specifier order`(declaration: String, expected: String) = check(declaration, expected)

  @ParameterizedTest(name = "{0} is {1}")
  @DisplayName("qualifiers do not change the type, wherever they are written")
  @CsvSource(
    "const int x, CSignedInt",
    "int const x, CSignedInt", // east-const
    "volatile int x, CSignedInt",
    "int volatile x, CSignedInt",
    "const unsigned long x, CUnsignedLong",
    "unsigned long const x, CUnsignedLong",
    "const char *x, CPointer<CSignedChar>",
    "char const *x, CPointer<CSignedChar>", // east-const
    "static int x, CSignedInt",
    "extern int x, CSignedInt",
    "static const int x, CSignedInt",
  )
  fun `qualifiers`(declaration: String, expected: String) = check(declaration, expected)

  @ParameterizedTest(name = "{0} is {1}")
  @DisplayName("pointers")
  @CsvSource(
    "int *x, CPointer<CSignedInt>",
    "int **x, CPointer<CPointer<CSignedInt>>",
    "unsigned long *x, CPointer<CUnsignedLong>",
    "void *x, CPointer<CVoid>",
  )
  fun `pointers`(declaration: String, expected: String) = check(declaration, expected)

  @ParameterizedTest(name = "{0} is {1}")
  @DisplayName("structs, however the qualifier is written")
  @CsvSource(
    "struct S *x, CPointer<CStruct>",
    "const struct S *x, CPointer<CStruct>",
    "struct S const *x, CPointer<CStruct>", // east-const: the bug this suite was written for
    "volatile struct S *x, CPointer<CStruct>",
    "struct S volatile *x, CPointer<CStruct>",
  )
  fun `struct qualifiers`(declaration: String, expected: String) =
    check(declaration, expected, prelude = "struct S { int a; int b; };")

  @ParameterizedTest(name = "{0} is {1}")
  @DisplayName("typedef names, however the qualifier is written")
  @CsvSource(
    "T *x, CPointer<CStruct>",
    "const T *x, CPointer<CStruct>",
    "T const *x, CPointer<CStruct>", // east-const through a typedef
    "T volatile *x, CPointer<CStruct>",
  )
  fun `typedef'd struct qualifiers`(declaration: String, expected: String) =
    check(declaration, expected, prelude = "struct S { int a; int b; }; typedef struct S T;")

  @ParameterizedTest(name = "{0} is {1}")
  @DisplayName("typedef names of scalar types")
  @CsvSource(
    "myint x, CSignedInt",
    "const myint x, CSignedInt",
    "myint const x, CSignedInt", // east-const through a scalar typedef
    "myint *x, CPointer<CSignedInt>",
    "myuint x, CUnsignedLong",
    "myuint const x, CUnsignedLong",
  )
  fun `typedef'd scalars`(declaration: String, expected: String) =
    check(declaration, expected, prelude = "typedef int myint; typedef unsigned long myuint;")
}
