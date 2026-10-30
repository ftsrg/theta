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
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

/**
 * The CLI rebuilds the frontend in-process when it revises the memory model or the arithmetic, so a
 * second build of an input in the same JVM must behave like a fresh one. The static struct registry
 * used to survive between builds: the typedef below then resolved to the previous build's type, and
 * the element copy was refused as an unhandled left-hand side.
 */
class RepeatedBuildTest {

  @Test
  fun secondBuildInSameJvmSucceeds() {
    val source =
      """
      struct Elem { unsigned char a; unsigned char b; };
      typedef struct Elem ELEM;
      struct Table { unsigned char n; ELEM e[3]; };
      typedef struct Table *PTABLE;
      void copy(PTABLE t, unsigned long i) { t->e[0] = t->e[i]; }
      int main() {
        struct Table t;
        t.e[1].a = 5;
        copy(&t, 1);
        return t.e[0].a;
      }
      """
        .trimIndent()
    for (attempt in 1..2) {
      val (xcfa, _, _) =
        getXcfaFromC(
          source.byteInputStream(),
          ParseContext(),
          false,
          XcfaProperty(ErrorDetection.ERROR_LOCATION),
          NullLogger.getInstance(),
        )
      assertTrue(xcfa.procedures.isNotEmpty(), "build $attempt must produce an XCFA")
    }
  }
}
