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
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.ArchitectureType
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.model.StmtLabel
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.DisplayName
import org.junit.jupiter.api.Test

/**
 * `struct S s = other;` has to actually copy.
 *
 * The struct branch of the declaration handling type-checked the initializer and then emitted
 * nothing, so the variable was declared and never written: every field of `s` stayed unconstrained
 * and the solver could read whatever it liked out of it. The statement form (`s = other;`) always
 * worked -- only the *initializer* form was dropped -- and the initializer form is what a
 * struct-returning function looks like at the call site (`struct aws_byte_buf buf =
 * aws_byte_buf_from_array(a, len);`), so the aws-c-common harnesses asserted on an uninitialised
 * struct.
 *
 * A copy shows up as a write through the struct's memory (a `MemoryAssignStmt`). With the
 * initializer dropped there is no write *at all* -- the struct is only ever read -- so the presence
 * of one is the assertion. (One is enough: the copy aliases the source object rather than
 * duplicating it, so the source's own write serves both.)
 */
class StructInitTest {

  private fun memoryWrites(body: String): Int {
    val parseContext = ParseContext()
    parseContext.architecture = ArchitectureType.LP64
    val (xcfa, _, _) =
      getXcfaFromC(
        """
        extern unsigned long __VERIFIER_nondet_ulong(void);
        struct T { unsigned long len; };
        struct T mk(unsigned long n) { struct T t; t.len = n; return t; }
        int main(void) {
          unsigned long n = __VERIFIER_nondet_ulong();
          $body
          return (int) sink;
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
      .count { it is MemoryAssignStmt<*, *, *> }
  }

  @Test
  @DisplayName("a struct copy-initialised from a returned struct is actually copied")
  fun structCopyInitFromCall() {
    // `struct T b = a;` reaches the same branch, but does not make a test that can fail: `a`'s own
    // `a.len = n` is a write either way, and the copy *aliases* `a` rather than adding a second
    // one,
    // so the count is 1 with the fix and without it. Initialising from a call is the shape that
    // distinguishes -- and it is the shape the aws harnesses actually use: with the initializer
    // dropped, nothing aliases the callee's struct, so its write is dead and gets removed too,
    // leaving no write at all and `b.len` reading unconstrained memory.
    assertTrue(
      memoryWrites("struct T b = mk(n); unsigned long sink = b.len;") > 0,
      "`struct T b = mk(n);` must write b, not just declare it",
    )
  }
}
