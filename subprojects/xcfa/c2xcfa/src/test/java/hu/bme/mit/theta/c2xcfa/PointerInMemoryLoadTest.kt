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
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.anytype.Reference
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.grammar.function.FunctionVisitor
import hu.bme.mit.theta.frontend.transformation.grammar.parseTypeAware
import hu.bme.mit.theta.frontend.transformation.model.statements.CProgram
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.model.SequenceLabel
import hu.bme.mit.theta.xcfa.model.StmtLabel
import org.antlr.v4.runtime.CharStreams
import org.junit.jupiter.api.Assertions.assertFalse
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

/**
 * Loading a pointer value out of an array of pointers -- `int *d = *(dataArray + 2)` (equivalently
 * `dataArray[2]`) -- must be a plain dereference `arrays[dataArray][2]`, whose result is the stored
 * pointer. Two bugs conspired to turn it into `ref(deref(dataArray, deref(0, 2)))`, a pointer *into*
 * `dataArray` at a nonsense offset read out of the null object:
 * 1. `p + 2` lost its pointer type in `getSmallestCommonType`, so the sum was integer arithmetic
 *    wrapped in a modulo -- which both truncated the base and hid the `AddExpr` from the `*(p + i)`
 *    fold, so `*(dataArray + 2)` no longer became `deref(dataArray, 2)`.
 * 2. Even once it did, the assignment path's `hasArithmetic` recursed into the load's own offset,
 *    mistook the load for pointer arithmetic, and rewrote `d = deref(dataArray, 2)` into
 *    `d = &dataArray[deref(0, 2)]`.
 *
 * The net effect was a false `valid-deref` on the whole Juliet CWE476 `*(dataArray + k)` family.
 * This pins the lowering directly (pre-pass, before ReferenceElimination folds bases to literals).
 */
class PointerInMemoryLoadTest {

  private fun assignmentTo(varName: String, body: String): AssignStmt<*> {
    val src = "int **glob;\nint main(){\n int **pp = glob;\n$body\n return 0;\n}\n"
    val parseContext = ParseContext()
    val program =
      parseTypeAware(CharStreams.fromStream(src.byteInputStream()))
        .accept(FunctionVisitor(parseContext, NullLogger.getInstance()))
    check(program is CProgram)
    val builder =
      FrontendXcfaBuilder(
          parseContext,
          XcfaProperty(ErrorDetection.ERROR_LOCATION),
          NullLogger.getInstance(),
        )
        .buildXcfa(program)
    val assigns =
      builder.getProcedures().flatMap { p ->
        p.getEdges().flatMap { e ->
          (e.label as? SequenceLabel)?.labels.orEmpty().plus(e.label).mapNotNull {
            ((it as? StmtLabel)?.stmt as? AssignStmt<*>)
          }
        }
      }
    return assigns.first { it.varDecl.name.endsWith("::$varName") }
  }

  private fun collectDerefs(e: hu.bme.mit.theta.core.type.Expr<*>): List<Dereference<*, *, *>> =
    (if (e is Dereference<*, *, *>) listOf(e) else emptyList()) + e.ops.flatMap { collectDerefs(it) }

  private fun hasReference(e: hu.bme.mit.theta.core.type.Expr<*>): Boolean =
    e is Reference<*, *> || e.ops.any { hasReference(it) }

  @Test
  fun loadOfPointerFromArrayIsAPlainDereference() {
    // int *d = *(pp + 2);  -- load the pointer stored at pp[2].
    val assign = assignmentTo("d", "int *d = *(pp + 2U); if (*d != 5) { }")
    val rhs = assign.expr
    // The loaded value is a dereference, not an address-of: `&pp[...]` would make `d` alias into
    // `pp` instead of holding the stored pointer.
    assertFalse(hasReference(rhs), "a pointer load must not be re-read as an address-of: $rhs")
    val derefs = collectDerefs(rhs)
    assertTrue(derefs.isNotEmpty(), "the load must be a dereference: $rhs")
    val load = derefs.first()
    // Dereferences the base variable `pp` directly (a RefExpr), not a nested dereference of the
    // null object (`deref(0, ...)`), and not pointer arithmetic folded into the base.
    assertTrue(
      load.array is RefExpr<*> && (load.array as RefExpr<*>).decl.name.endsWith("::pp"),
      "the load must dereference `pp` directly, got base ${load.array}",
    )
    assertFalse(
      load.array is Dereference<*, *, *>,
      "the load base must not itself be a dereference (the deref(0,..) mangling): $rhs",
    )
    // The constant index survives as the offset (printed as a unary-plus `(+ 2)`), and the offset
    // is not itself a dereference of the null object (the `deref(0, 2)` mangling).
    assertTrue(load.offset.toString().contains("2"), "the index must stay the offset: $rhs")
    assertTrue(collectDerefs(load.offset).isEmpty(), "the offset must not be a deref: $rhs")
  }

  @Test
  fun scalarLoadThroughPointerArithmeticKeepsIndexAsOffset() {
    // The scalar sibling: `int j = *(pi + 2)` was already handled, but guard it so the pointer fix
    // does not regress it -- base `pi`, offset `2`, no arithmetic folded into the base.
    val src =
      "int main(){ int *pi; int j = *(pi + 2U); if (j != 5) { } return 0; }"
    val parseContext = ParseContext()
    val program =
      parseTypeAware(CharStreams.fromStream(src.byteInputStream()))
        .accept(FunctionVisitor(parseContext, NullLogger.getInstance()))
    check(program is CProgram)
    val builder =
      FrontendXcfaBuilder(
          parseContext,
          XcfaProperty(ErrorDetection.ERROR_LOCATION),
          NullLogger.getInstance(),
        )
        .buildXcfa(program)
    val derefs =
      builder.getProcedures().flatMap { p ->
        p.getEdges().flatMap { e ->
          (e.label as? SequenceLabel)?.labels.orEmpty().plus(e.label).flatMap {
            ((it as? StmtLabel)?.stmt as? AssignStmt<*>)?.let { a -> collectDerefs(a.expr) }
              ?: emptyList()
          }
        }
      }
    assertTrue(
      derefs.any { it.array is RefExpr<*> && it.offset.toString().contains("2") },
      "*(pi + 2) must dereference pi at offset 2: $derefs",
    )
  }
}
