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
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.MemoryAssignStmt
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.anytype.RefExpr
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
 * Copying a scalar *through* two split pointers is one memory write, not a pointer store.
 *
 * `ReferenceElimination` splits a pointer that is used with arithmetic (`++from`) into `<v>_base` and
 * `<v>_offset`. Storing a *pointer value* to memory then has to write both halves to two channels;
 * but `*to = *from` where the value is a `char` stores a single scalar. It was misclassified: the
 * split var `from` appears inside the value expression `*from`, only as the *address* being read
 * through, and that was counted as a stored pointer. The store was then split into two -- one of them
 * `arrays[to_offset][…] := arrays[from_offset][…]`, a dereference *through the offset variable as if
 * it were a base*. Its bounds check read `__theta_ptr_size[from_offset]` (an unallocated object, size
 * 0) and reported a spurious invalid dereference -- the whole `openbsd_*strcpy-alloca`/`strcpy_small`
 * cluster.
 *
 * The correct lowering derefs only through the base (`arrays[to_base][to_offset]`), so no memory
 * write may address the *offset* half of a split pointer -- which is what is asserted here.
 */
class SplitPointerScalarCopyTest {

  @Test
  @DisplayName("a scalar copy through split pointers never dereferences the offset half")
  fun scalarCopyDoesNotDerefOffset() {
    val parseContext = ParseContext()
    parseContext.architecture = ArchitectureType.LP64
    val (xcfa, _, _) =
      getXcfaFromC(
        """
        extern void *__builtin_alloca(unsigned long);
        void cp(char *to, const char *from) { for (; (*to = *from) != 0; ++from, ++to); }
        int main(void) {
          char *a = (char*) __builtin_alloca(4);
          char *s = (char*) __builtin_alloca(2);
          s[0] = 0;
          cp(a, s);
          return 0;
        }
        """
          .trimIndent()
          .byteInputStream(),
        parseContext,
        false,
        XcfaProperty(ErrorDetection.ERROR_LOCATION),
        NullLogger.getInstance(),
      )
    val memWrites =
      xcfa.procedures
        .flatMap { it.edges }
        .flatMap { it.getFlatLabels() }
        .filterIsInstance<StmtLabel>()
        .map { it.stmt }
        .filterIsInstance<MemoryAssignStmt<*, *, *>>()

    // The copy is present: a write through a `_base` pointer (the split pointer folded to its base).
    assertTrue(
      memWrites.any { w ->
        ((w.deref as? Dereference<*, *, *>)?.array as? RefExpr<*>)?.decl?.name?.endsWith("_base") ==
          true
      },
      "the scalar copy must still write through the pointer's base",
    )
    // But never through an `_offset` half used as a base -- that was the fabricated bogus dereference.
    val offsetAsBase =
      memWrites.filter { w ->
        val a = (w.deref as? Dereference<*, *, *>)?.array
        (a is RefExpr<*> && (a.decl as VarDecl<*>).name.endsWith("_offset"))
      }
    assertTrue(
      offsetAsBase.isEmpty(),
      "no memory write may dereference the offset half of a split pointer (found: $offsetAsBase)",
    )
  }
}
