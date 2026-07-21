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
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.ArithmeticType
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.XcfaProperty
import org.junit.jupiter.api.Assertions.assertThrows
import org.junit.jupiter.api.Test

/**
 * `p = q + i` stores no offset in a pointer value (an object id), so it used to be refused with
 * "Pointer arithmetic not supported". It is now read as `p = &q[i]` -- `ref(deref(q, i))` -- and
 * [hu.bme.mit.theta.xcfa.passes.ReferenceElimination] splits `p` into a `base` / `offset` pair that
 * gives the offset a home. This is how CIL spells every array and field access: `tmp = base + idx;
 * *tmp`.
 *
 * Building the program is the assertion: on a regression these throw (the frontend refusal, or a
 * "bare use of split variable" from the pass), so `buildBoth` reaching its end is a pass.
 */
class PointerArithmeticTest {

  private fun build(src: String, arithmetic: ArithmeticType) {
    val parseContext = ParseContext()
    parseContext.architecture = ArchitectureType.ILP32
    parseContext.arithmetic = arithmetic
    getXcfaFromC(
      src.byteInputStream(),
      parseContext,
      false,
      XcfaProperty(ErrorDetection.ERROR_LOCATION),
      NullLogger.getInstance(),
    )
  }

  private fun buildBoth(src: String) {
    build(src, ArithmeticType.bitvector)
    build(src, ArithmeticType.integer)
  }

  private fun main(body: String) = "extern void reach_error(); int main() { $body return 0; }"

  @Test
  fun `taking the address of an array element builds`() {
    buildBoth(main("int a[10]; int *p = &a[3]; *p = 5; if (a[3] != 5) reach_error();"))
  }

  @Test
  fun `a pointer plus an integer assigned to a pointer builds`() {
    buildBoth(main("int a[10]; int *p = a + 3; *p = 5; if (a[3] != 5) reach_error();"))
  }

  @Test
  fun `a pointer minus an integer builds`() {
    buildBoth(
      main("int a[10]; int *q = &a[7]; int *p = q - 4; *p = 5; if (a[3] != 5) reach_error();")
    )
  }

  @Test
  fun `a pointer routed through an integer and back builds`() {
    // A cast to a same-or-wider integer cannot change a pointer's value, so it is a `Pos` no-op (no
    // modulo) and the pointer survives the round trip -- including its offset, when it is one of
    // the
    // base/offset split variables.
    buildBoth(
      main("int a[10]; int *p = a; unsigned long q = (unsigned long)p; int *r = (int *)q; *r = 5;")
    )
  }

  @Test
  fun `a split pointer routed through an integer and back keeps its offset`() {
    buildBoth(
      main(
        "int a[10]; int *p = &a[3]; unsigned long q = (unsigned long)p; int *r = (int *)q;" +
          " *r = 5; if (a[3] != 5) reach_error();"
      )
    )
  }

  @Test
  fun `chained pointer arithmetic through a reused intermediate builds`() {
    // The base of the second step is itself a split pointer, so this exercises the composing branch
    // (`p_base = q_base`, `p_offset = q_offset + i`) rather than re-addressing a bare split
    // variable.
    buildBoth(
      main(
        "int a[10]; int *q = a; int *p = q + 7; int *r = p - 4; *r = 5; if (a[3] != 5) reach_error();"
      )
    )
  }

  // --- Scalar uses of split pointers: comparisons and pointer difference. ---
  //
  // `decomposeScalarPointerOp` lets a split pointer appear bare in a comparison or an additive
  // difference instead of throwing "bare use of split variable" -- previously the *only* legal
  // bare use was re-addressing (`ref(deref(...))`) or a plain copy. These tests guard the shapes
  // that motivated the change: they must build under both arithmetics, exactly like the pass's
  // existing pointer-arithmetic tests above -- the assertion is that construction does not throw.
  // (The reach_error conditions document the intended arithmetic for a human reader; verifying them
  // requires actually running the solver, which is out of scope for this build-level test file.)

  @Test
  fun `pointer difference between two split pointers builds`() {
    // Both operands are split (each is `&a[i]`), so this is the base case the frontend spells as
    // `Add(p, Neg(q))`: the bases must cancel and only the offsets (7 and 2) remain, `p - q == 5`.
    buildBoth(
      main("int a[10]; int *p = &a[7]; int *q = &a[2]; int d = p - q; if (d != 5) reach_error();")
    )
  }

  @Test
  fun `cstrlen shape - pointer difference between a split pointer and a plain parameter builds`() {
    // This is the shape that motivated the whole change: `p = s; while (*p) p++; return p - s;`.
    // `p` becomes split (through `p++`, i.e. `p = &p[1]`) but the parameter `s` is never split, so
    // `p - s` mixes a split operand with a plain one -- the plain operand's offset channel must
    // fall back to 0 rather than the whole expression being refused as a bare split use.
    buildBoth(
      """
      extern void reach_error();
      int cstrlen(const char *s) {
        const char *p = s;
        while (*p) p++;
        return p - s;
      }
      int main() {
        char buf[4] = {'a', 'b', 'c', 0};
        if (cstrlen(buf) != 3) reach_error();
        return 0;
      }
      """
        .trimIndent()
    )
  }

  @Test
  fun `a pointer difference with an extra integer term builds`() {
    // Exercises the n-ary `Add` shape the frontend emits for `p - 1 - s`: three signed terms (split
    // `p` positive, integer literal `1` negative, plain pointer `s` negative). The literal is not a
    // pointer operand at all, so it must be carried through as its own value (subtracted once) while
    // still cancelling the two pointer bases -- distinct from the plain two-term `p - q` case above.
    buildBoth(
      main(
        "int a[10]; int *p = &a[7]; int *s = a; int d = p - 1 - s; if (d != 6) reach_error();"
      )
    )
  }

  @Test
  fun `pointer comparisons between split pointers build`() {
    // `==`/`!=` must compare *both* channels (base and offset) -- two split pointers into different
    // objects must compare unequal even if their offsets coincide -- while `<` (and by extension
    // `<=`, `>`, `>=`) compares only the offset, since C defines ordering only within one object.
    buildBoth(
      main(
        "int a[10]; int *p = &a[3]; int *q = &a[3]; int *r = &a[5]; " +
          "if (!(p == q)) reach_error(); if (p != q) reach_error(); " +
          "if (!(p < r)) reach_error(); if (r < p) reach_error();"
      )
    )
  }

  @Test
  fun `a split pointer compared against the null pointer constant builds`() {
    // `0` is not a `RefExpr`, so it is not itself split -- this exercises the "one side is split, the
    // other is a bare literal" branch of the channel decomposition, where the literal's base/offset
    // channels fall back to (its rewritten value, offset 0) instead of a split pair.
    buildBoth(
      main("int a[10]; int *p = &a[3]; if (p == 0) reach_error(); if (!(p != 0)) reach_error();")
    )
  }

  @Test
  fun `loading a pointer through a dereference into a later-split variable is still refused`() {
    // `p = *q` loads a pointer *value* that was stored to memory. A stored split pointer writes its
    // base and offset to two separate channels (see the `MemoryAssignStmt` handling), so reading it
    // back through a single dereference and forcing the offset to 0 (as the plain-copy branch does
    // for `p = s`) would silently drop a stored mid-object offset and address the wrong cell later.
    // `flatPointerValue` only accepts a bare variable or a literal on the right-hand side, so a
    // `Dereference` must still fall through to the bare-use refusal -- this is what is pinned here,
    // guarding against a future, more permissive rewrite of that check.
    assertThrows(IllegalStateException::class.java) {
      buildBoth(
        """
        extern void reach_error();
        int use(int **q) {
          int *p = *q;
          p++;
          return *p;
        }
        int main() {
          int a[2];
          int *p1 = a;
          int *q = p1;
          return use(&q);
        }
        """
          .trimIndent()
      )
    }
  }

  @Test
  fun `passing a split pointer as a function argument is still refused`() {
    // Out of scope on purpose: a mid-object pointer *value* cannot escape as an argument (or a
    // return value) because the split model has nowhere to carry a non-zero offset across a call
    // boundary -- `seedSplitParams` only ever seeds a callee's split parameter at offset 0, which
    // presumes the caller passed a plain (offset-0) pointer. Guards that widening bare uses into
    // scalar contexts did not also, by accident, legalize a split pointer escaping by value.
    assertThrows(IllegalStateException::class.java) {
      buildBoth(
        """
        extern void reach_error();
        int use(int *x) { return *x; }
        int main() {
          int a[10];
          int *p = &a[3];
          int y = use(p);
          if (y != 0) reach_error();
          return 0;
        }
        """
          .trimIndent()
      )
    }
  }
}
