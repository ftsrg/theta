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
 * `--ptr-size-in-memory` must not change an OC verdict, under each memory model it supports (byte
 * views need bytes). The two-block programs check that the size cells of different objects do not
 * overlap.
 */
class XcfaCliPtrSizeInMemoryTest {
  companion object {
    private val programs =
      listOf(
        "free_ok.c" to "Safe",
        "oob_read.c" to "Unsafe",
        "use_after_free.c" to "Unsafe",
        "double_free.c" to "Unsafe",
        "byte_view_ok.c" to "Safe",
        "byte_view_oob.c" to "Unsafe",
        "two_blocks_ok.c" to "Safe",
        "two_blocks_oob.c" to "Unsafe",
      )

    @JvmStatic
    fun tasks(): Stream<Arguments> =
      listOf("bytes", "flat", "multi")
        .flatMap { model ->
          listOf(false, true).flatMap { inMemory ->
            programs
              .filter { (file, _) -> model == "bytes" || !file.startsWith("byte_view") }
              .map { (file, expected) -> Arguments.of(file, model, inMemory, expected) }
          }
        }
        .stream()
  }

  @ParameterizedTest
  @MethodSource("tasks")
  fun testOcVerdict(file: String, model: String, inMemory: Boolean, expected: String) {
    val dir = "/c/ptr-size-in-memory"
    val params =
      arrayOf(
        "--input-type",
        "C",
        "--input",
        javaClass.getResource("$dir/$file")!!.path,
        "--property",
        javaClass.getResource("$dir/valid-memsafety.prp")!!.path,
        "--memory-model",
        model,
        "--backend",
        "OC",
        *(if (inMemory) arrayOf("--ptr-size-in-memory") else emptyArray()),
        "--stacktrace",
        "--debug",
        "--output-directory",
        createTempDirectory().absolutePathString(),
      )
    val verdict = runCatchingOutput(params).lines().lastOrNull { "SafetyResult" in it } ?: ""
    assertTrue("SafetyResult $expected" in verdict) {
      "Expected $expected for $file ($model, in memory: $inMemory), got $verdict"
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
