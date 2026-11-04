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
import hu.bme.mit.theta.frontend.transformation.grammar.function.FunctionVisitor
import hu.bme.mit.theta.frontend.transformation.grammar.parseTypeAware
import hu.bme.mit.theta.frontend.transformation.model.statements.CCall
import hu.bme.mit.theta.frontend.transformation.model.statements.CCompound
import hu.bme.mit.theta.frontend.transformation.model.statements.CProgram
import org.antlr.v4.runtime.CharStreams
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertFalse
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

/** What linking several units in [FunctionVisitor.visitTranslationUnits] has to get right. */
class MultiTranslationUnitTest {

  private fun link(vararg units: String): CProgram =
    FunctionVisitor(ParseContext(), NullLogger.getInstance())
      .visitTranslationUnits(units.map { parseTypeAware(CharStreams.fromString(it)) })

  private fun CProgram.functionNames() = functions.map { it.funcDecl.name }

  private fun CProgram.globalNames() = globalDeclarations.map { it.get2().name }

  @Test
  fun mainCanBeInAnyUnitAndReachesAcrossThem() {
    val program =
      link(
        "int used(void) { return 1; } int unused(void) { return 2; }",
        "int used(void); int main(void) { return used(); }",
      )
    assertEquals(setOf("used", "main"), program.functionNames().toSet())
  }

  @Test
  fun internalNamesOfUnitsAreDifferentObjects() {
    val program =
      link(
        "static int x = 1; static int f(void) { return x; } int g(void) { return f(); }",
        "static int x = 2; static int f(void) { return x; } int g(void); int main(void) { return f() + g(); }",
      )
    assertEquals(setOf("f__tu0", "f__tu1", "g", "main"), program.functionNames().toSet())
    assertEquals(setOf("x__tu0", "x__tu1"), program.globalNames().toSet())
  }

  @Test
  fun anInternalNameDoesNotClashWithAnExternalOne() {
    val program =
      link(
        "int f(void) { return 1; } int g(void) { return f(); }",
        "static int f(void) { return 2; } int g(void); int main(void) { return f() + g(); }",
      )
    assertEquals(setOf("f", "f__tu1", "g", "main"), program.functionNames().toSet())
  }

  @Test
  fun anExternalGlobalIsOneObjectInitialisedByItsDefinition() {
    val program =
      link(
        "extern int x; int main(void) { return x; }",
        "extern int x; int x = 5;",
        "extern int x; int get(void) { return x; }",
      )
    val decls = program.globalDeclarations.filter { it.get2().name == "x" }
    assertEquals(1, decls.size)
    assertTrue(decls.single().get1().initExpr != null)
  }

  @Test
  fun aStrongDefinitionWinsOverWeakOnes() {
    val program =
      link(
        "__attribute__((weak)) int f(void) { return 1; } int main(void) { return f(); }",
        "int f(void) { return 2; }",
        "__attribute__((weak)) int f(void) { return 3; }",
      )
    assertEquals(1, program.functionNames().count { it == "f" })
    assertTrue(program.functions.single { it.funcDecl.name == "f" }.sourceText.contains("return 2"))
  }

  @Test
  fun aUnitCanCallItsDefinitionThatLostToAnotherUnits() {
    val program =
      link(
        "__attribute__((weak)) int f(void) { return 1; } int g(void) { return f(); }",
        "int f(void) { return 2; } int g(void); int main(void) { return g(); }",
      )
    assertEquals(setOf("f", "g", "main"), program.functionNames().toSet())
  }

  @Test
  fun constructorsRunBeforeMainInUnitOrder() {
    val program =
      link(
        "__attribute__((constructor)) static void first(void) {} int main(void) { return 0; }",
        "__attribute__((constructor)) static void second(void) {}",
      )
    val body = program.functions.single { it.funcDecl.name == "main" }.compound as CCompound
    val calls = body.getcStatementList().filterIsInstance<CCall>().map { it.functionId }
    assertEquals(listOf("first", "second"), calls)
  }

  @Test
  fun tagsBelongToTheirUnit() {
    val program =
      link(
        "struct S { int a; }; int f(void) { struct S s = {1}; return s.a; }",
        "struct S { char b; long c; }; int f(void); int main(void) { struct S s = {1, 2}; return (int)s.c + f(); }",
      )
    assertFalse(program.functions.isEmpty())
  }
}
