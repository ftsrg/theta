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
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.model.AtomicBeginLabel
import hu.bme.mit.theta.xcfa.model.InvokeLabel
import hu.bme.mit.theta.xcfa.model.XcfaLabel
import org.junit.jupiter.api.Assertions.assertFalse
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

/**
 * The GCC `__atomic_*` builtins have no declaration to resolve, so they used to abort the frontend
 * with "No such variable or macro". They are now emitted as calls and lowered by
 * `AtomicFunctionsPass` into memory operations (wrapped in an atomic block when the program is
 * multi-threaded). This pins that: no atomic call survives into the built XCFA, and a concurrent
 * read-modify-write becomes a genuine atomic block.
 */
class AtomicBuiltinsTest {

  private fun labelsOf(src: String): List<XcfaLabel> {
    val parseContext = ParseContext()
    val (xcfa, _, _) =
      getXcfaFromC(
        src.byteInputStream(),
        parseContext,
        false,
        XcfaProperty(ErrorDetection.ERROR_LOCATION),
        NullLogger.getInstance(),
      )
    fun flatten(l: XcfaLabel): List<XcfaLabel> =
      when (l) {
        is hu.bme.mit.theta.xcfa.model.SequenceLabel -> l.labels.flatMap { flatten(it) }
        is hu.bme.mit.theta.xcfa.model.NondetLabel -> l.labels.flatMap { flatten(it) }
        else -> listOf(l)
      }
    return xcfa.procedures.flatMap { p -> p.edges.flatMap { flatten(it.label) } }
  }

  @Test
  fun atomicBuiltinsAreLoweredAwayInSingleThreadedCode() {
    val labels =
      labelsOf(
        """
        int main() {
          int x = 0, e = 0;
          __atomic_store_n(&x, 1, 0);
          int v = __atomic_load_n(&x, 0);
          int o = __atomic_fetch_add(&x, 2, 0);
          int ok = __atomic_compare_exchange_n(&x, &e, 9, 0, 0, 0);
          __atomic_thread_fence(0);
          if (v != o) { return 1; }
          return 0;
        }
        """
          .trimIndent()
      )
    assertFalse(
      labels.any { it is InvokeLabel && it.name.contains("atomic") },
      "no __atomic_* call may survive lowering: ${labels.filterIsInstance<InvokeLabel>().map { it.name }}",
    )
  }

  @Test
  fun concurrentReadModifyWriteBecomesAnAtomicBlock() {
    val labels =
      labelsOf(
        """
        #include <pthread.h>
        int x = 0;
        void *thr(void *a) {
          __atomic_fetch_add(&x, 1, 0);
          return 0;
        }
        int main() {
          pthread_t t;
          pthread_create(&t, 0, thr, 0);
          pthread_join(t, 0);
          return 0;
        }
        """
          .trimIndent()
      )
    assertFalse(
      labels.any { it is InvokeLabel && it.name.contains("atomic") },
      "no __atomic_* call may survive lowering",
    )
    assertTrue(
      labels.any { it is AtomicBeginLabel },
      "a concurrent atomic RMW must be wrapped in an atomic block",
    )
  }
}
