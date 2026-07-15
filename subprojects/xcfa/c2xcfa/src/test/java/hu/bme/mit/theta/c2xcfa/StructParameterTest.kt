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
import org.junit.jupiter.api.DisplayName
import org.junit.jupiter.api.Test

/**
 * A struct argument is passed *by value*: copied into a fresh object the callee is handed.
 *
 * A struct's value is its base id, so passing the variable passed the caller's object -- the callee's
 * parameter took the same base, and a write to a by-value parameter (`void f(struct T t){ t.len = 9;
 * }`) was read back by the caller. C copies at the call, so the argument is copied into a new object
 * and the callee gets that object's base.
 *
 * The fingerprint is that copy: a write that reads a field of one object and writes the same field of
 * *another* (`arrays[argtmp][i] := arrays[a][i]`), one per field. Without the fix the argument is
 * passed by reference and no such cross-object copy exists at all. (The fixture has no other struct
 * assignment, so the copies counted here are the argument's.)
 *
 * The object copied into is a stack allocation like any other local, so it is held by a temporary
 * whose base is drawn at run time -- two threads calling the function at once must not copy into one
 * shared object. That is why the two sides are compared as expressions rather than as constants.
 */
class StructParameterTest {

  /** Writes that copy a field from one object's base to a *different* object's base. */
  private fun crossObjectFieldCopies(body: String): List<MemoryAssignStmt<*, *, *>> {
    val parseContext = ParseContext()
    parseContext.architecture = ArchitectureType.LP64
    val (xcfa, _, _) =
      getXcfaFromC(
        """
        extern unsigned long __VERIFIER_nondet_ulong(void);
        struct T { unsigned long len; unsigned long cap; };
        void f(struct T t) { t.len = 9; t.cap = 9; }
        int main(void) {
          struct T a;
          a.len = __VERIFIER_nondet_ulong();
          a.cap = 1;
          $body
          return (int) a.len;
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
      .filter { stmt ->
        val toBase = (stmt.deref as? Dereference<*, *, *>)?.array
        val fromBase = (stmt.expr as? Dereference<*, *, *>)?.array
        toBase != null && fromBase != null && toBase != fromBase
      }
  }

  @Test
  @DisplayName("a struct argument is copied into a fresh object, not passed by reference")
  fun structArgumentIsCopied() {
    val copies = crossObjectFieldCopies("f(a);")
    assertEquals(
      2,
      copies.size,
      "`f(a)` must copy a's two fields into the argument object, not pass a's base (copies: $copies)",
    )
  }

  @Test
  @DisplayName("no copy is made when nothing is passed by value")
  fun noCallNoCopy() {
    // The control: without the call there is no argument to copy, so the fix must not invent one.
    assertEquals(0, crossObjectFieldCopies("").size, "there is no by-value argument here")
  }
}
