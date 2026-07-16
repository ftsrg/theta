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
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.ArchitectureType
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.model.ChoiceType
import hu.bme.mit.theta.xcfa.model.StmtLabel
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import org.junit.jupiter.api.Assertions.assertFalse
import org.junit.jupiter.api.DisplayName
import org.junit.jupiter.api.Test

/**
 * The value of an assignment expression is the value assigned, taken at the assignment -- not a later
 * re-read of the destination.
 *
 * `while ((*s1++ = *s2++))` tests the value of the assignment. The value is the copied `char`; the
 * post-increments `s1++`/`s2++` are side effects that run before the next sequence point. The value
 * used to be `getExpression()` = the destination lvalue `*s1`, re-read *after* `s1++` had moved the
 * pointer -- so the guard read uninitialised memory one past the copy, the loop ran on, and the next
 * iteration read `*s2` out of bounds (the openbsd/`strcpy_small` alloca `valid-deref` false alarms).
 *
 * The value is now snapshotted at the assignment, so the loop-guard test is over that scalar and
 * never re-dereferences the moved pointer -- which is what is asserted: no branch condition of the
 * loop dereferences anything.
 */
class AssignmentValuePostIncrementTest {

  @Test
  @DisplayName("a post-increment assignment used as a loop guard is not re-read through the pointer")
  fun guardTestsTheSnapshotNotTheMovedLvalue() {
    val parseContext = ParseContext()
    parseContext.architecture = ArchitectureType.LP64
    val (xcfa, _, _) =
      getXcfaFromC(
        """
        extern void *__builtin_alloca(unsigned long);
        void cp(char *s1, const char *s2) { while ((*s1++ = *s2++)); }
        int main(void) {
          char *a = (char*) __builtin_alloca(4);
          char *b = (char*) __builtin_alloca(2);
          b[0] = 0;
          cp(a, b);
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
    // The loop's two guard branches are the only conditional assumes here. Their condition must be
    // over the snapshotted value, so it must not dereference memory. Before the fix it was
    // `Neq(deref(s1_base, s1_offset), 0)` -- a dereference of the *already incremented* pointer.
    val branchConditionsDereference =
      xcfa.procedures
        .flatMap { it.edges }
        .flatMap { it.getFlatLabels() }
        .filterIsInstance<StmtLabel>()
        .filter { it.choiceType != ChoiceType.NONE }
        .map { it.stmt }
        .filterIsInstance<AssumeStmt>()
        .any { assume -> dereferences(assume.cond) }

    assertFalse(
      branchConditionsDereference,
      "the loop guard must test the assignment's snapshotted value, not re-dereference the moved pointer",
    )
  }

  private fun dereferences(expr: hu.bme.mit.theta.core.type.Expr<*>): Boolean =
    expr is Dereference<*, *, *> || expr.ops.any { dereferences(it) }
}
