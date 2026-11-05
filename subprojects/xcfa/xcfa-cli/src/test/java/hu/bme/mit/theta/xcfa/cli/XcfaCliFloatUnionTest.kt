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

import hu.bme.mit.theta.xcfa.cli.XcfaCli.Companion.main
import java.io.BufferedOutputStream
import java.io.FileOutputStream
import java.io.PrintStream
import java.util.stream.Stream
import kotlin.io.path.absolutePathString
import kotlin.io.path.createTempDirectory
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.MethodSource

/**
 * Floating-point union members store their IEEE bits. The bits of a NaN are any NaN pattern, so a
 * counterexample that needs one must not be reported (nan-payload.c is safe when compiled by gcc).
 */
class XcfaCliFloatUnionTest {
  companion object {
    @JvmStatic
    fun programs(): Stream<Arguments> =
      Stream.of(
        Arguments.of("bits-safe.c", "Safe"),
        Arguments.of("nan-roundtrip-safe.c", "Safe"),
        Arguments.of("bits-unsafe.c", "Unsafe"),
        Arguments.of("nan-payload.c", "Unknown"),
      )
  }

  @ParameterizedTest
  @MethodSource("programs")
  fun testBmcVerdict(file: String, expected: String) {
    val params =
      arrayOf(
        "--input-type",
        "C",
        "--input",
        javaClass.getResource("/c/float-union/$file")!!.path,
        "--backend",
        "BOUNDED",
        "--no-interpolation",
        "--no-induction",
        "--stacktrace",
        "--output-directory",
        createTempDirectory().absolutePathString(),
      )
    val verdict = runCatchingOutput(params).lines().lastOrNull { "SafetyResult" in it } ?: ""
    assertTrue("SafetyResult $expected" in verdict) { "Expected $expected for $file, got $verdict" }
  }

  private fun runCatchingOutput(params: Array<String>): String {
    val output = createTempDirectory().resolve("stdout_stderr_combined").toFile()
    PrintStream(BufferedOutputStream(FileOutputStream(output)), true).use { ps ->
      val savedSysOut = System.out
      val savedSysErr = System.err
      System.setOut(ps)
      System.setErr(ps)
      try {
        main(params)
      } catch (e: IllegalStateException) {
        if (e.message != "Done debugging") throw e
      } finally {
        System.setOut(savedSysOut)
        System.setErr(savedSysErr)
        print(output.readText())
      }
    }
    return output.readText()
  }
}
