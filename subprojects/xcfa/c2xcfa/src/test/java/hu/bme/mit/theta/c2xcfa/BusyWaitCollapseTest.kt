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
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import hu.bme.mit.theta.xcfa.model.XcfaProcedure
import hu.bme.mit.theta.xcfa.passes.UnrollPass
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.DisplayName
import org.junit.jupiter.api.Test

/**
 * `--collapse-busy-waits` replaces a waiting loop with a single iteration of itself, which is sound
 * only when every iteration is interchangeable with every other. These two cases are the boundary.
 *
 * The one that must be refused is the reason the criterion asks a *position-sensitive* question. It
 * reads `v` on a path that has not written `v` yet, so the read takes the previous iteration's
 * value -- and neither of the two properties that look like they would catch that does: no value is
 * computed from its own previous value, and `v` is written on *every* path, so it is written by the
 * time the loop is left. Collapsing it loses the only execution that reaches the error.
 */
class BusyWaitCollapseTest {

  private fun program(watcherBody: String) =
    """
    extern void reach_error(void);
    typedef unsigned long int pthread_t;
    typedef union { char __size[56]; long int __align; } pthread_attr_t;
    extern int pthread_create (pthread_t *__restrict __newthread,
          const pthread_attr_t *__restrict __attr,
          void *(*__start_routine) (void *),
          void *__restrict __arg);
    extern int pthread_join (pthread_t __th, void **__thread_return);

    volatile int a = 0;
    int reached = 0;

    void *watcher(void *p) {
      $watcherBody
      reached = 1;
      return 0;
    }

    void *mover(void *p) {
      __atomic_store_n(&a, 1, 5);
      __atomic_store_n(&a, 2, 5);
      return 0;
    }

    int main(void) {
      pthread_t t1, t2;
      pthread_create(&t1, 0, watcher, 0);
      pthread_create(&t2, 0, mover, 0);
      pthread_join(t1, 0);
      pthread_join(t2, 0);
      if (reached == 1) reach_error();
      return 0;
    }
    """

  /** How many loops the thread procedure still contains after the passes have run. */
  private fun loopsInWatcher(watcherBody: String, collapse: Boolean): Int {
    UnrollPass.COLLAPSE_BUSY_WAITS = collapse
    try {
      val parseContext = ParseContext()
      parseContext.architecture = ArchitectureType.ILP32
      val (xcfa, _, _) =
        getXcfaFromC(
          program(watcherBody).trimIndent().byteInputStream(),
          parseContext,
          false,
          XcfaProperty(ErrorDetection.ERROR_LOCATION),
          NullLogger.getInstance(),
        )
      return xcfa.procedures.filter { it.name.contains("watcher") }.sumOf { backEdges(it) }
    } finally {
      UnrollPass.COLLAPSE_BUSY_WAITS = false
    }
  }

  /** The number of edges that close a cycle, i.e. how many loops [proc] contains. */
  private fun backEdges(proc: XcfaProcedure): Int {
    var count = 0
    val onStack = mutableSetOf<XcfaLocation>()
    val finished = mutableSetOf<XcfaLocation>()
    fun visit(loc: XcfaLocation) {
      onStack.add(loc)
      for (edge in loc.outgoingEdges) {
        if (edge.target in onStack) count++ else if (edge.target !in finished) visit(edge.target)
      }
      onStack.remove(loc)
      finished.add(loc)
    }
    visit(proc.initLoc)
    return count
  }

  private val spinning =
    "int o = __atomic_load_n(&a, 5); while (o != 2) { o = __atomic_load_n(&a, 5); }"

  private val readsBeforeWriting =
    "int o, v = 0, t = 0;" +
      " while (1) {" +
      "   o = __atomic_load_n(&a, 5);" +
      "   if (o == 1) { v = 1; t = 0; } else { t = v; v = 2; }" +
      "   if (o == 2 && t == 1) break;" +
      " }"

  @Test
  @DisplayName("a loop that only polls is replaced by one iteration of itself")
  fun pollingLoopCollapses() {
    assertEquals(
      1,
      loopsInWatcher(spinning, collapse = false),
      "the loop should be there to begin with",
    )
    assertEquals(
      0,
      loopsInWatcher(spinning, collapse = true),
      "every iteration of a poll is interchangeable with every other, so one of them is enough",
    )
  }

  @Test
  @DisplayName("a loop that reads a variable a path has not written yet is refused")
  fun loopCarriedReadIsRefused() {
    assertEquals(
      1,
      loopsInWatcher(readsBeforeWriting, collapse = true),
      "the else path reads the previous iteration's v, which one iteration cannot reproduce",
    )
  }
}
