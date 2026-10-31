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
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.CsvSource

/**
 * `<errno.h>` error numbers. The header is not preprocessed, so the names have to resolve as
 * modelled macros -- otherwise `return EINVAL;` stops the frontend.
 */
class ErrnoTest {

  @ParameterizedTest(name = "{0} = {1}")
  @CsvSource("EINVAL, 22", "ENOMEM, 12", "EBUSY, 16", "ETIMEDOUT, 110", "EWOULDBLOCK, 11")
  fun `errno macros resolve to their Linux values`(name: String, value: Int) {
    val parseContext = ParseContext()
    parseContext.architecture = ArchitectureType.ILP32
    val (xcfa, _, _) =
      getXcfaFromC(
        """
        #include <errno.h>
        int main() { int e = $name; return e; }
        """
          .trimIndent()
          .byteInputStream(),
        parseContext,
        false,
        XcfaProperty(ErrorDetection.ERROR_LOCATION),
        NullLogger.getInstance(),
      )
    val labels = xcfa.procedures.flatMap { it.edges }.joinToString("\n") { it.label.toString() }
    assertTrue(Regex("\\b$value\\b").containsMatchIn(labels), "$name must become $value:\n$labels")
  }
}
