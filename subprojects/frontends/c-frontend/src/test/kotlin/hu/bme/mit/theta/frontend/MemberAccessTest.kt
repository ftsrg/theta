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

import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.frontend.transformation.grammar.function.FunctionVisitor
import hu.bme.mit.theta.frontend.transformation.grammar.parseTypeAware
import hu.bme.mit.theta.frontend.transformation.model.statements.CProgram
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CArray
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CStruct
import org.antlr.v4.runtime.CharStreams
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertFalse
import org.junit.jupiter.api.Assertions.assertNull
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

/** The members a program accesses are recorded by their struct type. */
class MemberAccessTest {

  private val memcmp = "extern int memcmp(const void *, const void *, unsigned long);"

  private fun parse(src: String): Pair<ParseContext, CProgram> {
    val parseContext = ParseContext()
    val program =
      parseTypeAware(CharStreams.fromString(src))
        .accept(FunctionVisitor(parseContext, NullLogger.getInstance()))
    return parseContext to program as CProgram
  }

  private fun CProgram.typeOf(name: String) =
    globalDeclarations.first { it.get1().name == name }.get1().actualType

  private fun CProgram.structOf(name: String) = typeOf(name) as CStruct

  @Test
  fun directAndPointerAccessesAreRecorded() {
    val (parseContext, program) =
      parse(
        "struct S { int a; int b; int c; } s; struct T { int t; } t;" +
          " int main() { struct S *p = &s; struct T *q = &t; return s.a + p->b; }"
      )
    val s = program.structOf("s")
    assertTrue(parseContext.isMemberAccessed(s, "a"))
    assertTrue(parseContext.isMemberAccessed(s, "b"))
    assertFalse(parseContext.isMemberAccessed(s, "c"))
    assertTrue(parseContext.isAnyMemberAccessed(s))
    assertFalse(parseContext.isAnyMemberAccessed(program.structOf("t")))
  }

  @Test
  fun memcmpAccessesEveryMemberOfItsOperands() {
    val (parseContext, program) =
      parse(
        "struct In { int x; int y; }; struct S { int a; struct In in[2]; } s1, s2;" +
          " struct T { int t; } t; $memcmp int main() { struct T *q = &t; return memcmp(&s1, &s2, sizeof(s1)); }"
      )
    val s = program.structOf("s1")
    val inner = (s.fieldsAsMap["in"] as CArray).embeddedType as CStruct
    listOf(s to "a", s to "in", inner to "x", inner to "y").forEach { (type, member) ->
      assertTrue(parseContext.isMemberAccessed(type, member), member)
    }
    assertFalse(parseContext.isAnyMemberAccessed(program.structOf("t")))
  }

  @Test
  fun memcmpOnArraysAccessesTheirElements() {
    val (parseContext, program) =
      parse(
        "struct S { int a; } s1[2], s2[2]; char b1[4], b2[4]; $memcmp" +
          " int main() { return memcmp(s1, s2, sizeof(s1)) + memcmp(b1, b2, 4); }"
      )
    val s = (program.typeOf("s1") as CArray).embeddedType as CStruct
    assertTrue(parseContext.isMemberAccessed(s, "a"))
  }

  @Test
  fun everyMemberIsAccessedOnceAnAccessCannotBeAttributed() {
    val (parseContext, program) =
      parse("struct S { int a; } s; int main() { struct S *p = &s; return 0; }")
    val s = program.structOf("s")
    assertFalse(parseContext.isAnyMemberAccessed(s))
    parseContext.markEveryMemberAccessed()
    assertTrue(parseContext.isAnyMemberAccessed(s))
    assertTrue(parseContext.isMemberAccessed(s, "a"))
  }

  @Test
  fun enclosingStaticUnionIsTheOutermostOne() {
    val parseContext = ParseContext()
    parseContext.recordStaticObject(1.toBigInteger(), true, null)
    parseContext.recordStaticObject(4.toBigInteger(), false, 1.toBigInteger())
    parseContext.recordStaticObject(7.toBigInteger(), true, 4.toBigInteger())
    parseContext.recordStaticObject(10.toBigInteger(), false, null)
    assertEquals(1.toBigInteger(), parseContext.enclosingStaticUnion(7.toBigInteger()))
    assertEquals(1.toBigInteger(), parseContext.enclosingStaticUnion(4.toBigInteger()))
    assertNull(parseContext.enclosingStaticUnion(10.toBigInteger()))
    assertTrue(parseContext.isStaticObject(7.toBigInteger()))
    assertFalse(parseContext.isStaticObject(2.toBigInteger()))
  }
}
