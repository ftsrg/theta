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
package hu.bme.mit.theta.xcfa.analysis

import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.algorithm.bounded.BoundedChecker
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.c2xcfa.getXcfaFromC
import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.analysis.monolithic.XcfaPipelineChecker
import hu.bme.mit.theta.xcfa.analysis.proof.LocationInvariants
import hu.bme.mit.theta.xcfa.model.NondetLabel
import hu.bme.mit.theta.xcfa.utils.getAllLabels
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.assertThrows

/** A bounded engine with block encoding counts loop iterations, not edges. */
class BlockEncodingTest {

  private val header =
    """
    extern int __VERIFIER_nondet_int(void);
    extern void abort(void);
    void reach_error() { abort(); }
    void __VERIFIER_assert(int cond) { if (!cond) { reach_error(); } }
    void assume_abort_if_not(int cond) { if (!cond) { abort(); } }
    int a, b, c, last;
    """
      .trimIndent()

  // The shape of the Hardness tasks: each iteration recomputes values, and the assertion
  // re-checks them. Every iteration passes many edges.
  private val step =
    """
    last = a;
    b = __VERIFIER_nondet_int();
    assume_abort_if_not(b > -1000 && b < 1000);
    if (b > 10) { if (last > 0) a = b + 1; else a = b - 1; } else { a = last; }
    if (a > 100) c = 1; else c = 0;
    if (b < 0) { if (c) a = a + 1; }
    """
      .trimIndent()

  private val property =
    "(b < 0 && c) || ((b > 10 ? (last > 0 ? a == b + 1 : a == b - 1) : a == last) && c == (a > 100))"

  private fun check(
    src: String,
    blockEncoding: Boolean,
    maxBound: Int,
  ): SafetyResult<LocationInvariants, Trace<XcfaState<PtrState<ExplState>>, XcfaAction>> {
    val parseContext = ParseContext()
    val property = XcfaProperty(ErrorDetection.ERROR_LOCATION)
    val xcfa =
      getXcfaFromC(src.byteInputStream(), parseContext, false, property, NullLogger.getInstance())
        .first
    val factory = Z3LegacySolverFactory.getInstance()
    return XcfaPipelineChecker(
        xcfa,
        property,
        parseContext,
        { monolithicExpr ->
          BoundedChecker(
            monolithicExpr = monolithicExpr,
            shouldGiveUp = { it > maxBound },
            bmcSolver = factory.createSolver(),
            indSolver = factory.createSolver(),
            logger = NullLogger.getInstance(),
          )
        },
        acceptUnreliableSafe = false,
        blockEncoding = blockEncoding,
      )
      .check()
  }

  @Test
  fun kInductionClosesAfterFewBlocks() {
    val src = "$header\nint main() { while (1) { $step __VERIFIER_assert($property); } }"
    assertTrue(check(src, blockEncoding = true, maxBound = 3).isSafe)
    assertTrue(check(src, blockEncoding = false, maxBound = 3).let { !it.isSafe && !it.isUnsafe })
  }

  @Test
  fun aLoopFreeProgramIsOneBlock() {
    val src = "$header\nint main() { $step $step $step __VERIFIER_assert($property); }"
    assertTrue(check(src, blockEncoding = true, maxBound = 2).isSafe)
    assertTrue(check(src, blockEncoding = false, maxBound = 2).let { !it.isSafe && !it.isUnsafe })
  }

  // longjmp stays an unresolved call: removing it would remove the jump back to setjmp.
  @Test
  fun aCallAfterTheLastErrorPathIsNotDropped() {
    val src =
      """
      $header
      typedef void* jmp_buf;
      extern int setjmp(jmp_buf env);
      extern void longjmp(jmp_buf env, int val);
      jmp_buf buf;
      int main() {
        volatile int count = 0;
        setjmp(buf);
        __VERIFIER_assert(count == 0);
        if (count < 5) { count++; longjmp(buf, 1); }
      }
      """
        .trimIndent()
    assertThrows<IllegalArgumentException> { check(src, blockEncoding = true, maxBound = 5) }
    assertThrows<IllegalArgumentException> { check(src, blockEncoding = false, maxBound = 5) }
  }

  @Test
  fun aCounterexampleHasTheOriginalLabels() {
    val src = "$header\nint main() { while (1) { $step __VERIFIER_assert(a != 42); } }"
    val result = check(src, blockEncoding = true, maxBound = 5)
    assertTrue(result.isUnsafe)
    val labels = result.asUnsafe().cex.actions.flatMap { it.label.getAllLabels() }
    assertTrue(labels.none { it is NondetLabel })
    assertTrue(labels.none { "__block_choice_" in it.toString() })
  }
}
