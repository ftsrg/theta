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
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.type.abstracttype.AddExpr
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
 * A stack array is an `alloca` block, not a `malloc`+`free` one.
 *
 * A local array's base used to come from `malloc` -- heap memory (`3k+0`) the program is responsible
 * for freeing, so the frontend also emitted a `free` at scope exit. That is the wrong model: the
 * memory is released when the function returns, not by the program, and the free made a returned
 * block look doubly freed and a block declared in a loop look leaked. `alloca` states it directly --
 * the block goes in the free residue class (`3k+1`, not scanned for leaks, never freeable) and gets
 * a *fresh runtime* base, so two activations of the function cannot alias.
 *
 * Both `malloc` and `alloca` lower to `base := __malloc (+ residue)`; what tells them apart is the
 * residue, `+1` for `alloca` against a bare `__malloc` for `malloc`. The allocation feeding the
 * array is asserted to carry that `+1`.
 */
class StackArrayAllocaTest {

  @Test
  @DisplayName("a local array is allocated from the alloca residue, not malloc")
  fun localArrayUsesAlloca() {
    val parseContext = ParseContext()
    parseContext.architecture = ArchitectureType.ILP32
    val (xcfa, _, _) =
      getXcfaFromC(
        """
        extern int __VERIFIER_nondet_int(void);
        int main(void) {
          int arr[4];
          arr[0] = __VERIFIER_nondet_int();
          return arr[0];
        }
        """
          .trimIndent()
          .byteInputStream(),
        parseContext,
        false,
        XcfaProperty(ErrorDetection.ERROR_LOCATION),
        NullLogger.getInstance(),
      )
    val counterAdds =
      xcfa.procedures
        .flatMap { it.edges }
        .flatMap { it.getFlatLabels() }
        .filterIsInstance<StmtLabel>()
        .map { it.stmt }
        .filterIsInstance<AssignStmt<*>>()
        // base := __malloc + residue, capturing the allocation's residue
        .mapNotNull { it.expr as? AddExpr<*> }
        .filter { add -> add.ops.any { it is RefExpr<*> && (it.decl.name == "__malloc") } }

    assertTrue(counterAdds.isNotEmpty(), "the array must be allocated from the __malloc counter")
    // `malloc` assigns a bare `__malloc` (a plain ref, no Add); only `alloca` adds the `+1` residue,
    // so an Add over `__malloc` at all is the alloca fingerprint. The bump `__malloc := __malloc + 3`
    // adds a literal 3; the allocation adds 1.
    assertTrue(
      counterAdds.any { add ->
        add.ops.any { op -> op.toString().let { it == "1" || it.endsWith(" 1") } }
      },
      "a stack array must take the alloca residue (__malloc + 1), not malloc's bare base: $counterAdds",
    )
  }
}
