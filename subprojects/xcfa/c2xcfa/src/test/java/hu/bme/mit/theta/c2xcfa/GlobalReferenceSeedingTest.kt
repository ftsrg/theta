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
import hu.bme.mit.theta.core.stmt.MemoryAssignStmt
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.ArchitectureType
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.ArithmeticType
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.model.StmtLabel
import hu.bme.mit.theta.xcfa.model.XcfaProcedure
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.DisplayName
import org.junit.jupiter.api.Test

/**
 * When only a *thread body* takes the address of a global (`&y`),
 * [hu.bme.mit.theta.xcfa.passes.ReferenceElimination] must still process `main`: `main` is the init
 * procedure, so it alone can seed the synthetic `y*` pointer (and its allocation size under
 * memsafety), and `main`'s own accesses to `y` must be rewritten onto the same dereference the
 * threads use. `main` itself ends up with no `Reference` label — its only `&` was the
 * `pthread_create(&t, ...)` handle, consumed by CLibraryFunctionsPass — so an early-out on "this
 * procedure has no references" left `y*` unseeded (every thread deref then false-alarms
 * `valid-deref`: the whole pthread-wmm cluster) and left `main` writing plain `y` while the threads
 * read `__arrays[y*][0]` (split storage, unsound in both directions).
 *
 * With the seed in place, constant propagation folds the base id into the derefs, so the pinned
 * post-fix shape is: no plain assignment to `y` survives anywhere, and `main` and the thread write
 * `y` through a dereference *on the same base*.
 */
class GlobalReferenceSeedingTest {

  private val program =
    """
    typedef unsigned long pthread_t;
    extern int pthread_create(pthread_t *__newthread, void *__attr, void *(*__start_routine)(void *), void *__arg);
    int y = 0;
    int *p;
    void *thr(void *arg) { p = &y; y = 1; return 0; }
    int main() {
      pthread_t t;
      pthread_create(&t, 0, thr, 0);
      y = 2;
      return 0;
    }
    """
      .trimIndent()

  private fun XcfaProcedure.stmts() =
    edges.flatMap { it.getFlatLabels() }.filterIsInstance<StmtLabel>().map { it.stmt }

  private fun sharedStorageFor(arithmetic: ArithmeticType): Boolean {
    val parseContext = ParseContext()
    parseContext.architecture = ArchitectureType.ILP32
    parseContext.arithmetic = arithmetic
    val (xcfa, _, _) =
      getXcfaFromC(
        program.byteInputStream(),
        parseContext,
        false,
        XcfaProperty(ErrorDetection.ERROR_LOCATION),
        NullLogger.getInstance(),
      )
    val main = xcfa.initProcedures.map { it.first }.single()
    val thread = xcfa.procedures.single { it != main }

    val plainYWrites =
      xcfa.procedures
        .flatMap { it.stmts() }
        .filterIsInstance<AssignStmt<*>>()
        .filter { it.varDecl.name == "y" }
    val mainBases =
      main.stmts().filterIsInstance<MemoryAssignStmt<*, *, *>>().map { it.deref.array }
    val threadBases =
      thread.stmts().filterIsInstance<MemoryAssignStmt<*, *, *>>().map { it.deref.array }

    return plainYWrites.isEmpty() && mainBases.intersect(threadBases.toSet()).isNotEmpty()
  }

  @Test
  @DisplayName("a global referred only from a thread shares one storage with main (integer)")
  fun globalSharedStorageInteger() {
    assertTrue(
      sharedStorageFor(ArithmeticType.integer),
      "main (the init procedure) must be processed even though its own &t was consumed by " +
        "CLibraryFunctionsPass: its y accesses must go through the same dereference base the " +
        "thread uses — otherwise y* is unseeded (false valid-deref alarms) and the stores split",
    )
  }

  @Test
  @DisplayName("a global referred only from a thread shares one storage with main (bitvector)")
  fun globalSharedStorageBitvector() {
    assertTrue(
      sharedStorageFor(ArithmeticType.bitvector),
      "main (the init procedure) must be processed even though its own &t was consumed by " +
        "CLibraryFunctionsPass: its y accesses must share the thread's dereference base",
    )
  }
}
