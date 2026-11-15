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
 * A call through a function pointer reaches the function it points to, whatever its signature: the
 * call has no prototype, so its values are converted to the callee's types. A callee whose types
 * differ from the call's values used to be dropped from the dispatch, silently skipping the call.
 */
class XcfaCliFunctionPointerTest {
  companion object {
    private val programs =
      listOf(
        "void_callee.c" to "Unsafe",
        "pointer_param.c" to "Unsafe",
        "converted_ok.c" to "Safe",
        "narrow_return_ok.c" to "Safe",
        "narrow_return_bad.c" to "Unsafe",
        "vtable_ok.c" to "Safe",
        "vtable_bad.c" to "Unsafe",
      )

    private val variants =
      listOf(
        listOf("--arithmetic", "integer"),
        listOf("--arithmetic", "bitvector"),
        listOf("--arithmetic", "bitvector", "--memory-model", "flat"),
        listOf("--arithmetic", "bitvector", "--memory-model", "bytes"),
      )

    @JvmStatic
    fun tasks(): Stream<Arguments> =
      programs
        .flatMap { (file, expected) ->
          // BMC takes minutes on the vtable programs in the byte-level memory model
          variants
            .filter { !file.startsWith("vtable") || "bytes" !in it }
            .map { Arguments.of(file, it, expected) }
        }
        .stream()
  }

  @ParameterizedTest
  @MethodSource("tasks")
  fun testBmcVerdict(file: String, options: List<String>, expected: String) {
    val dir = "/c/function-pointers"
    val params =
      arrayOf(
        "--input-type",
        "C",
        "--input",
        javaClass.getResource("$dir/$file")!!.path,
        "--property",
        javaClass.getResource("$dir/unreach-call.prp")!!.path,
        *options.toTypedArray(),
        "--backend",
        "BOUNDED",
        "--stacktrace",
        "--output-directory",
        createTempDirectory().absolutePathString(),
      )
    val verdict = runCatchingOutput(params).lines().lastOrNull { "SafetyResult" in it } ?: ""
    assertTrue("SafetyResult $expected" in verdict) {
      "Expected $expected for $file ($options), got $verdict"
    }
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
      } finally {
        System.setOut(savedSysOut)
        System.setErr(savedSysErr)
      }
    }
    return output.readText()
  }
}
