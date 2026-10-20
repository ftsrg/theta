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
package hu.bme.mit.theta.xcfa.cli

import hu.bme.mit.theta.c2xcfa.getXcfaFromC
import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.cli.serialization.XcfaFiles
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.serialization.XcfaSerialization
import java.io.File
import kotlinx.serialization.SerializationException
import org.junit.jupiter.api.Assertions.assertArrayEquals
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertThrows
import org.junit.jupiter.api.Test
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.ValueSource

/** A worker must get exactly the XCFA its parent built, however often and in whichever format. */
class XcfaSerializationTest {

  private fun build(fixture: String): Pair<XCFA, ParseContext> {
    val parseContext = ParseContext()
    val (xcfa, _, _) =
      getXcfaFromC(
        File("canaries/fixtures/$fixture").inputStream(),
        parseContext,
        false,
        XcfaProperty(ErrorDetection.ERROR_LOCATION),
        NullLogger.getInstance(),
      )
    return xcfa to parseContext
  }

  @ParameterizedTest
  @ValueSource(
    strings =
      [
        "byte_addressed_union.c",
        "packed_bitfields.c",
        "union_punning.c",
        "designated_init.c",
        "nested_aggregate_init.c",
        "memcpy_struct_cells.c",
      ]
  )
  fun encodingIsDeterministicAndSurvivesARoundTrip(fixture: String) {
    val (xcfa, parseContext) = build(fixture)
    val bytes = XcfaFiles.encode(xcfa, parseContext)
    assertArrayEquals(bytes, XcfaFiles.encode(xcfa, parseContext))
    val (decoded, decodedContext) = XcfaFiles.decode(bytes)
    assertArrayEquals(bytes, XcfaFiles.encode(decoded, decodedContext))

    val json = XcfaFiles.json
    val hash = XcfaFiles.formatHash
    val text = XcfaSerialization.encodeToString(json, hash, xcfa, parseContext)
    val (fromJson, fromJsonContext) = XcfaSerialization.decodeFromString(json, hash, text)
    assertEquals(text, XcfaSerialization.encodeToString(json, hash, fromJson, fromJsonContext))
  }

  @Test
  fun theBuiltFormatHashIsCurrent() {
    assertEquals(XcfaSerialization.computeFormatHash(XcfaFiles.module), XcfaFiles.formatHash)
  }

  @Test
  fun anotherFormatIsRefused() {
    val (xcfa, parseContext) = build("union_punning.c")
    val hash = XcfaFiles.formatHash
    val text = XcfaSerialization.encodeToString(XcfaFiles.json, hash, xcfa, parseContext)
    val stale = text.replaceFirst("\"$hash\"", "\"0\"")
    assertThrows(SerializationException::class.java) {
      XcfaSerialization.decodeFromString(XcfaFiles.json, hash, stale)
    }
  }
}
