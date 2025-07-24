/*
 *  Copyright 2025 Budapest University of Technology and Economics
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

import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.chc.ChcFrontend
import hu.bme.mit.theta.frontend.chc.ChcFrontend.ChcTransformation
import hu.bme.mit.theta.xcfa.passes.ChcPasses
import hu.bme.mit.theta.xcfa.toC
import java.io.FileInputStream
import java.util.stream.Stream
import kotlin.io.path.createTempDirectory
import org.antlr.v4.runtime.CharStreams
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.MethodSource

class XcfaToCTest {
  companion object {

    @JvmStatic
    fun chcFiles(): Stream<Arguments> {
      return Stream.of(
        Arguments.of("/chc/chc-LIA-Lin-Arrays_000.smt2", ChcFrontend.ChcTransformation.FORWARD),
        Arguments.of("/chc/chc-LIA-Arrays_000.smt2", ChcFrontend.ChcTransformation.BACKWARD),
      )
    }

    @JvmStatic
    fun dslFiles(): Stream<Arguments> {
      return Stream.of(Arguments.of("/dsl/async.xcfa.kts"), Arguments.of("/dsl/sync.xcfa.kts"))
    }
  }

  @ParameterizedTest
  @MethodSource("chcFiles")
  fun testRoundTrip(filePath: String, chcTransformation: ChcTransformation) {
    val chcFrontend = ChcFrontend(chcTransformation)
    val xcfa =
      chcFrontend
        .buildXcfa(
          CharStreams.fromStream(FileInputStream(javaClass.getResource(filePath)!!.path)),
          ChcPasses(ParseContext(), NullLogger.getInstance()),
        )
        .build()
    val temp = createTempDirectory()
    val file =
      temp.resolve("${filePath.split("/").last()}.c").also {
        it.toFile().writeText(xcfa.toC(ParseContext(), true, false, false))
      }
    System.err.println(file)
  }
}
