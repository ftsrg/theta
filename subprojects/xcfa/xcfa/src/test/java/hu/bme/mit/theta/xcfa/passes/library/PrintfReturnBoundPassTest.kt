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
package hu.bme.mit.theta.xcfa.passes.library

import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.ArchitectureType
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertNull
import org.junit.jupiter.api.Test

class PrintfReturnBoundPassTest {

  private fun bound(format: String, architecture: ArchitectureType = ArchitectureType.LP64) =
    PrintfReturnBoundPass(ParseContext().also { it.architecture = architecture })
      .maxFormattedLength(format)

  @Test
  fun `literal text and integer conversions are bounded`() {
    assertEquals(0L, bound(""))
    assertEquals(22L, bound("unknown uid %u"))
    assertEquals(11L, bound("%d"))
    assertEquals(1L, bound("%%"))
    assertEquals(4L, bound("%hhd"))
    assertEquals(20L, bound("%lu"))
    assertEquals(11L, bound("%ld", ArchitectureType.ILP32))
    assertEquals(10L, bound("%#x"))
    assertEquals(18L, bound("%p"))
  }

  @Test
  fun `width and precision raise the bound`() {
    assertEquals(11L, bound("%5d"))
    assertEquals(30L, bound("%30d"))
    assertEquals(41L, bound("%.40d"))
    assertEquals(3L, bound("%.3s"))
  }

  @Test
  fun `a conversion without a bound gives no bound`() {
    assertNull(bound("%s"))
    assertNull(bound("%*d"))
    assertNull(bound("%f"))
    assertNull(bound("%ls"))
    assertNull(bound("%n"))
    assertNull(bound("%"))
  }
}
