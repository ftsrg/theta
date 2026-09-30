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
import hu.bme.mit.theta.core.stmt.MemoryAssignStmt
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.MemoryModelType
import hu.bme.mit.theta.frontend.transformation.grammar.function.FunctionVisitor
import hu.bme.mit.theta.frontend.transformation.grammar.parseTypeAware
import hu.bme.mit.theta.frontend.transformation.model.statements.CProgram
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.model.NondetLabel
import hu.bme.mit.theta.xcfa.model.SequenceLabel
import hu.bme.mit.theta.xcfa.model.StmtLabel
import hu.bme.mit.theta.xcfa.model.XcfaLabel
import org.antlr.v4.runtime.CharStreams
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

/**
 * Writes to global objects that nothing reads are removed, and members nothing accesses are not
 * initialized; a union is only removed as a whole.
 */
class UnusedMemoryWriteTest {

  private fun memoryWrites(src: String, memoryModel: MemoryModelType = MemoryModelType.multi): Int {
    val (xcfa, _, _) =
      getXcfaFromC(
        src.trimIndent().byteInputStream(),
        ParseContext().also { it.memoryModel = memoryModel },
        false,
        XcfaProperty(ErrorDetection.ERROR_LOCATION),
        NullLogger.getInstance(),
      )
    return xcfa.procedures.sumOf { proc -> proc.edges.sumOf { writesIn(it.label) } }
  }

  /** The memory writes the frontend emits, before any pass could remove one. */
  private fun emittedWrites(src: String): Int {
    val parseContext = ParseContext()
    val program =
      parseTypeAware(CharStreams.fromString(src.trimIndent()))
        .accept(FunctionVisitor(parseContext, NullLogger.getInstance()))
    val builder =
      FrontendXcfaBuilder(
          parseContext,
          XcfaProperty(ErrorDetection.ERROR_LOCATION),
          NullLogger.getInstance(),
        )
        .buildXcfa(program as CProgram)
    return builder.getProcedures().sumOf { proc -> proc.getEdges().sumOf { writesIn(it.label) } }
  }

  private fun writesIn(label: XcfaLabel): Int =
    when (label) {
      is SequenceLabel -> label.labels.sumOf(::writesIn)
      is NondetLabel -> label.labels.sumOf(::writesIn)
      is StmtLabel -> if (label.stmt is MemoryAssignStmt<*, *, *>) 1 else 0
      else -> 0
    }

  @Test
  fun unusedMutexArrayIsNotInitialized() {
    val writes =
      memoryWrites(
        """
        #include <pthread.h>
        pthread_mutex_t m[10];
        int main() {
          pthread_mutex_lock(&m[0]);
          pthread_mutex_unlock(&m[0]);
          return 0;
        }
        """,
        MemoryModelType.flat,
      )
    assertEquals(0, writes)
  }

  @Test
  fun readsThroughPointersDoNotKeepUnaccessedMembers() {
    fun program(mutexes: Int) =
      """
      #include <pthread.h>
      extern void reach_error();
      pthread_mutex_t m[$mutexes];
      int x = 1;
      void *thr(void *arg) {
        if (*(int *)arg != 1) reach_error();
        pthread_mutex_lock(&m[0]);
        pthread_mutex_unlock(&m[0]);
        return 0;
      }
      int main() { pthread_t t; pthread_create(&t, 0, thr, &x); pthread_join(t, 0); return 0; }
      """
    val oneMutex = memoryWrites(program(1), MemoryModelType.flat)
    val tenMutexes = memoryWrites(program(10), MemoryModelType.flat)
    assertEquals(9, tenMutexes - oneMutex, "only the array cells of the extra mutexes are written")
  }

  @Test
  fun memcmpOperandsAreInitializedInEveryMember() {
    val declarations =
      "struct In { int x; int y; }; struct S { int a; struct In in; } s1, s2;" +
        " extern int memcmp(const void *, const void *, unsigned long);"
    val compared =
      emittedWrites("$declarations int main() { return s1.a + memcmp(&s1, &s2, sizeof(s1)); }")
    val allRead =
      emittedWrites("$declarations int main() { return s1.a + s1.in.x + s1.in.y + s2.a; }")
    assertEquals(allRead, compared)
  }

  @Test
  fun unreadStructFieldsAreNotInitialized() {
    val oneField = memoryWrites("struct S { int a; int b; int c; } s; int main() { return s.b; }")
    val allFields =
      memoryWrites("struct S { int a; int b; int c; } s; int main() { return s.a + s.b + s.c; }")
    assertTrue(oneField < allFields, "$oneField writes for one field, $allFields for all")
  }

  @Test
  fun readingOnePartOfAUnionKeepsAllOfIt() {
    val onePart =
      memoryWrites(
        """
        #include <pthread.h>
        pthread_mutex_t m;
        int main() { return m.__data.__kind; }
        """
      )
    val allParts =
      memoryWrites(
        """
        #include <pthread.h>
        pthread_mutex_t m;
        int main() { return m.__data.__kind + m.__data.__count + m.__data.__lock; }
        """
      )
    assertTrue(onePart > 0)
    assertEquals(allParts, onePart)
  }
}
