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
package hu.bme.mit.theta.xcfa.passes

import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test

class LibraryModelParsingTest {

  @Test
  fun `scanf conversions count the assigned arguments`() {
    assertEquals(1, scanConversions("%d"))
    assertEquals(2, scanConversions("%d %ld"))
    assertEquals(1, scanConversions("%*d %d"))
    assertEquals(1, scanConversions("100%% %5s"))
    assertEquals(1, scanConversions("%[^]a-z]"))
    assertEquals(0, scanConversions("text"))
  }

  @Test
  fun `scanf conversions are unknown with a percent n or a broken format`() {
    assertEquals(null, scanConversions("%d%n"))
    assertEquals(null, scanConversions("%hhn"))
    assertEquals(null, scanConversions("%"))
    assertEquals(null, scanConversions("%[abc"))
  }

  @Test
  fun `inet_aton forms give the host order value`() {
    assertEquals(0x7f000001L, parseIpv4("127.0.0.1"))
    assertEquals(0x7f000001L, parseIpv4("127.1"))
    assertEquals(0x0a010203L, parseIpv4("10.1.515"))
    assertEquals(0xc0a80001L, parseIpv4("0xc0.0250.0.1"))
    assertEquals(0xffffffffL, parseIpv4("4294967295"))
    assertEquals(0x01020304L, parseIpv4("1.2.3.4 trailing"))
  }

  @Test
  fun `invalid addresses are null`() {
    assertEquals(null, parseIpv4("256.0.0.1"))
    assertEquals(null, parseIpv4("1.2.3.4.5"))
    assertEquals(null, parseIpv4("1..2"))
    assertEquals(null, parseIpv4("08.1.1.1"))
    assertEquals(null, parseIpv4(""))
    assertEquals(null, parseIpv4("1.2.65536"))
  }
}
