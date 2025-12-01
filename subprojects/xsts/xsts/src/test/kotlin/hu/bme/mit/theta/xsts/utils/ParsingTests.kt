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
package hu.bme.mit.theta.xsts.utils

import hu.bme.mit.theta.xsts.XSTS
import hu.bme.mit.theta.xsts.dsl.XstsDslManager
import java.io.File
import java.util.stream.Stream
import kotlin.streams.asStream
import org.antlr.v4.runtime.misc.ParseCancellationException
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.MethodSource

class ParsingTests {

  companion object {
    @JvmStatic
    fun `Correct XSTS models should parse`(): Stream<File> {
      val correctDirectory = File("src/test/resources/valid-models")
      return correctDirectory.listFiles()?.asSequence()?.asStream() ?: Stream.of()
    }

    @JvmStatic
    fun `Incorrect XSTS models should fail to parse`(): Stream<File> {
      val incorrectDirectory = File("src/test/resources/syntaxerror-models")
      return incorrectDirectory.listFiles()?.asSequence()?.asStream() ?: Stream.of()
    }
  }

  fun tryParse(file: File): XSTS {
    return file.inputStream().use { XstsDslManager.createXsts(it) }
  }

  @ParameterizedTest
  @MethodSource
  fun `Correct XSTS models should parse`(file: File) {
    tryParse(file)
  }

  @ParameterizedTest
  @MethodSource
  fun `Incorrect XSTS models should fail to parse`(file: File) {
    Assertions.assertThrows(ParseCancellationException::class.java) { tryParse(file) }
  }
}
