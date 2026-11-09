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
 * `--library`: buf.c has no main. With get only, every client is safe; head reads the first byte of
 * a zero-sized buffer when a client constructs one from an empty source.
 */
class XcfaCliLibraryTest {
  companion object {
    @JvmStatic
    fun apis(): Stream<Arguments> =
      Stream.of(Arguments.of("safe.yml", "Safe"), Arguments.of("bad.yml", "Unsafe"))
  }

  @ParameterizedTest
  @MethodSource("apis")
  fun testLibraryVerdict(api: String, expected: String) {
    val dir = "/c/library"
    val out = createTempDirectory()
    val params =
      arrayOf(
        "--input-type",
        "C",
        "--input",
        javaClass.getResource("$dir/buf.c")!!.path,
        "--library",
        javaClass.getResource("$dir/$api")!!.path,
        "--property",
        javaClass.getResource("$dir/valid-memsafety.prp")!!.path,
        "--arithmetic",
        "integer",
        "--memory-model",
        "flat",
        "--memory-init",
        "UNCONSTRAINED",
        "--no-inlining",
        "--deref-to-array",
        "--backend",
        "CEGAR",
        "--domain",
        "PRED_CART",
        "--refinement",
        "BW_BIN_ITP",
        "--predsplit",
        "ATOMS",
        "--abstraction-solver",
        "JavaSMT:SMTINTERPOL",
        "--refinement-solver",
        "JavaSMT:SMTINTERPOL",
        "--stacktrace",
        "--debug",
        "--output-directory",
        out.absolutePathString(),
      )
    val verdict = runCatchingOutput(params).lines().lastOrNull { "SafetyResult" in it } ?: ""
    assertTrue("SafetyResult $expected" in verdict) { "Expected $expected for $api, got $verdict" }
    // the witness locations are lines of the generated client
    val witness = out.resolve("witness.yml").toFile()
    if (witness.exists()) assertTrue("'buf.library.c'" in witness.readText())
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
