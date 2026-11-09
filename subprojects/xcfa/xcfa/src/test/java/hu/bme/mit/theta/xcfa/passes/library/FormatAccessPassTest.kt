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

import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertNull
import org.junit.jupiter.api.Test

class FormatAccessPassTest {

  @Test
  fun plainStringsAreFound() {
    assertEquals(listOf(0, 2), stringArguments("%s %d %s\n"))
  }

  @Test
  fun precisionMayReadNothing() {
    assertEquals(listOf(0), stringArguments("%.2s"))
    assertEquals(listOf<Int>(), stringArguments("%.0s"))
  }

  @Test
  fun starsTakeArguments() {
    assertEquals(listOf(1), stringArguments("%*s"))
    assertEquals(listOf<Int>(), stringArguments("%.*s"))
  }

  @Test
  fun wideStringsAreLeftOut() {
    assertEquals(listOf<Int>(), stringArguments("%ls"))
  }

  @Test
  fun unknownConversionIsRefused() {
    assertNull(stringArguments("%y"))
  }

  @Test
  fun oneStringFormatCountsItsOtherCharacters() {
    assertEquals(2L, plainStringFormat("a%sb"))
    assertEquals(1L, plainStringFormat("%%%s"))
    assertNull(plainStringFormat("%s%s"))
    assertNull(plainStringFormat("%d"))
    assertNull(plainStringFormat("plain"))
  }
}
