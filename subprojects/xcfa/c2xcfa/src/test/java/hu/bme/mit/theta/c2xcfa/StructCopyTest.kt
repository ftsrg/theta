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
import hu.bme.mit.theta.core.stmt.MemoryAssignStmt
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.ArchitectureType
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.model.StmtLabel
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertNotEquals
import org.junit.jupiter.api.DisplayName
import org.junit.jupiter.api.Test

/**
 * `b = a` on structs copies a's contents into b. It must not make b *be* a.
 *
 * A struct variable's value is its base id, so assigning one struct to another assigned the base:
 * the two names then denoted a single object, and a write to the source after the copy was read back
 * through the destination -- `a.len = 1; b = a; a.len = 2;` left `b.len` reading 2. C copies at the
 * assignment, so the destination keeps the storage it was given and receives a's values into it,
 * which is a write per field: `arrays[b][i] := arrays[a][i]`.
 *
 * Those writes are what is asserted here -- one per field, each reading the source object and
 * writing the destination. The struct variables themselves do not survive to be asserted on: their
 * bases are literals, so they get constant-folded into the dereferences (`arrays[4][0] :=
 * arrays[1][0]`), which is also what makes the two objects visibly distinct below.
 */
class StructCopyTest {

  /** The field copies: memory writes that read a field of one object into a field of another. */
  private fun fieldCopies(body: String): List<Pair<Dereference<*, *, *>, Dereference<*, *, *>>> {
    val parseContext = ParseContext()
    parseContext.architecture = ArchitectureType.LP64
    val (xcfa, _, _) =
      getXcfaFromC(
        """
        extern unsigned long __VERIFIER_nondet_ulong(void);
        struct T { unsigned long len; unsigned long cap; };
        struct T mk(unsigned long n) { struct T t; t.len = n; t.cap = n + 1; return t; }
        int main(void) {
          unsigned long n = __VERIFIER_nondet_ulong();
          $body
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
      .filterIsInstance<MemoryAssignStmt<*, *, *>>()
      .mapNotNull { stmt -> (stmt.expr as? Dereference<*, *, *>)?.let { stmt.deref to it } }
  }

  private fun assertCopiesBothFields(
    copies: List<Pair<Dereference<*, *, *>, Dereference<*, *, *>>>,
    what: String,
  ) {
    assertEquals(2, copies.size, "$what must copy both fields of the struct (copies: $copies)")
    copies.forEach { (to, from) ->
      assertEquals(to.offset, from.offset, "a field has to be copied to the same field")
      assertNotEquals(
        to.array,
        from.array,
        "$what must write an object other than the one it reads (copies: $copies)",
      )
    }
    assertEquals(
      2,
      copies.map { it.first.offset }.distinct().size,
      "the two fields must be copied to different offsets (copies: $copies)",
    )
  }

  @Test
  @DisplayName("a struct assignment copies the source's fields into the destination")
  fun structAssignmentCopiesFields() {
    assertCopiesBothFields(
      fieldCopies("struct T a; struct T b; a.len = n; b = a; return (int) (b.len + b.cap);"),
      "`b = a`",
    )
  }

  @Test
  @DisplayName("a struct copy-initialised from a call copies the returned struct's fields")
  fun structCopyInitCopiesFields() {
    // The shape the aws-c-common harnesses use: `struct aws_byte_buf buf =
    // aws_byte_buf_from_array(a, len);`. It reaches the same assignment, through the initializer.
    assertCopiesBothFields(
      fieldCopies("struct T b = mk(n); return (int) (b.len + b.cap);"),
      "`struct T b = mk(n);`",
    )
  }
}
