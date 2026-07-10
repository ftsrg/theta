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
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.XcfaProperty
import org.junit.jupiter.api.Assertions.assertFalse
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

/**
 * `p->field` must lower to a single dereference `arrays[p][fieldIndex]`. It used to emit
 * `arrays[arrays[p][0]][fieldIndex]`, i.e. it read field 0's value and used it as a base address.
 * For heap pointers that base is unallocated, so every access through a malloc'd struct pointer was
 * reported as an invalid dereference (the dominant false `valid-deref` cluster).
 */
class PtrMemberAccessTest {

  private fun derefsOf(src: String): List<Dereference<*, *, *>> {
    val parseContext = ParseContext()
    val (xcfa, _, _) =
      getXcfaFromC(
        src.byteInputStream(),
        parseContext,
        false,
        XcfaProperty(ErrorDetection.ERROR_LOCATION),
        NullLogger.getInstance(),
      )
    val found = mutableListOf<Dereference<*, *, *>>()
    fun collect(expr: Expr<*>) {
      if (expr is Dereference<*, *, *>) found.add(expr)
      expr.ops.forEach { collect(it) }
    }
    xcfa.procedures.forEach { proc ->
      proc.edges.forEach { edge -> edge.label.collectExprs().forEach { collect(it) } }
    }
    return found
  }

  private fun hu.bme.mit.theta.xcfa.model.XcfaLabel.collectExprs(): List<Expr<*>> =
    when (this) {
      is hu.bme.mit.theta.xcfa.model.SequenceLabel -> labels.flatMap { it.collectExprs() }
      is hu.bme.mit.theta.xcfa.model.NondetLabel -> labels.flatMap { it.collectExprs() }
      is hu.bme.mit.theta.xcfa.model.StmtLabel -> stmt.ops()
      else -> emptyList()
    }

  private fun hu.bme.mit.theta.core.stmt.Stmt.ops(): List<Expr<*>> =
    when (this) {
      is hu.bme.mit.theta.core.stmt.AssignStmt<*> -> listOf(expr)
      is hu.bme.mit.theta.core.stmt.MemoryAssignStmt<*, *, *> -> listOf(deref, expr)
      is hu.bme.mit.theta.core.stmt.AssumeStmt -> listOf(cond)
      else -> emptyList()
    }

  private val heapStructProgram =
    """
    extern void *malloc(unsigned long);
    struct S { int a; int b; };
    int main() {
      struct S *p = malloc(sizeof(struct S));
      if (!p) return 0;
      p->a = 1;
      if (p->a != 1) { return 1; }
      return 0;
    }
    """
      .trimIndent()

  @Test
  fun ptrMemberAccessEmitsNoNestedDereference() {
    val derefs = derefsOf(heapStructProgram)
    assertTrue(derefs.isNotEmpty(), "the program must produce dereferences")
    assertFalse(
      derefs.any { it.array is Dereference<*, *, *> },
      "p->field must not dereference the result of another dereference",
    )
  }

  @Test
  fun pointerArithmeticBecomesDereferenceOffset() {
    // C defines *(p + i) as p[i]. Folding the index into the base makes the
    // pointer-validity model look up an unallocated object -> spurious valid-deref.
    val derefs =
      derefsOf(
        """
        int main() {
          static int a[10];
          int *p = a;
          int i = 2;
          if (*(p + i) != 0) { return 1; }
          return 0;
        }
        """
          .trimIndent()
      )
    assertTrue(derefs.isNotEmpty(), "the program must produce dereferences")
    assertTrue(
      derefs.any { d -> d.offset.toString() != "0" },
      "*(p + i) must dereference the base at a non-zero offset, not fold i into the base",
    )
    assertFalse(
      derefs.any { d -> d.array.toString().contains("+") },
      "the dereferenced base must not contain pointer arithmetic",
    )
  }

  @Test
  fun stackStructThroughPointerParamMatchesDirectAccess() {
    // A stack struct whose address is passed to a function: `a->field` inside the callee (a = &m)
    // and `m.field` in the caller must address the same cell. ReferenceElimination used to add an
    // extra indirection for bare reads of the referred struct variable but not for `&m`, so after
    // p->field became a single dereference the two desynced -> spurious counterexample.
    val derefs =
      derefsOf(
        """
        struct mutex { int is_locked; };
        void lock(struct mutex *a) { a->is_locked = 1; }
        int main() { struct mutex m; m.is_locked = 0; lock(&m); return 0; }
        """
          .trimIndent()
      )
    assertTrue(derefs.isNotEmpty(), "the program must produce dereferences")
    assertFalse(
      derefs.any { it.array is Dereference<*, *, *> },
      "member access on a referred struct variable must not be a double dereference",
    )
  }

  @Test
  fun sizeofStructTagIsNotZero() {
    // `sizeof(struct S)` used to fall through every lookup and warn
    // "sizeof got unknown type, using a literal 0 instead", so malloc(0).
    val parseContext = ParseContext()
    val warnings = StringBuilder()
    val logger =
      object :
        hu.bme.mit.theta.common.logging.BaseLogger(
          hu.bme.mit.theta.common.logging.Logger.Level.INFO
        ) {
        override fun writeStr(str: String) {
          warnings.append(str)
        }
      }
    getXcfaFromC(
      heapStructProgram.byteInputStream(),
      parseContext,
      false,
      XcfaProperty(ErrorDetection.ERROR_LOCATION),
      logger,
    )
    assertFalse(
      warnings.contains("sizeof got unknown type"),
      "sizeof(struct S) must resolve the struct tag",
    )
  }
}
