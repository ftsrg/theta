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
import hu.bme.mit.theta.xcfa.witnesses.WaypointContent
import hu.bme.mit.theta.xcfa.witnesses.WaypointType
import hu.bme.mit.theta.xcfa.witnesses.WitnessYamlConfig
import hu.bme.mit.theta.xcfa.witnesses.YamlWitness
import java.io.BufferedOutputStream
import java.io.File
import java.io.FileOutputStream
import java.io.PrintStream
import java.nio.file.Path
import java.util.stream.Stream
import kotlin.io.path.absolutePathString
import kotlin.io.path.createTempDirectory
import kotlinx.serialization.decodeFromString
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.MethodSource

/**
 * Source positions in violation witnesses, as the format defines them: a target is the first
 * character of the innermost full expression containing the violation, and a thread-registering
 * `function_enter` is the closing parenthesis of the `pthread_create` call. Validators other than
 * Theta match these positions exactly, so a round trip through Theta's own validator is not enough.
 * Each input of the target test marks its violation with a `// target: <code>` comment.
 */
class XcfaCliWitnessLocationTest {
  companion object {

    @JvmStatic
    fun targets(): Stream<Arguments> =
      Stream.of(
        Arguments.of("overflow-if-guard.c", "no-overflow"),
        Arguments.of("overflow-while-and.c", "no-overflow"),
        Arguments.of("overflow-for-test.c", "no-overflow"),
        Arguments.of("overflow-return.c", "no-overflow"),
        Arguments.of("overflow-initializer.c", "no-overflow"),
        Arguments.of("overflow-call-in-statement.c", "no-overflow"),
        Arguments.of("overflow-assert-argument.c", "no-overflow"),
        Arguments.of("deref-if-guard.c", "valid-memsafety"),
        Arguments.of("deref-memcpy.c", "valid-memsafety"),
      )

    @JvmStatic
    fun races(): Stream<Arguments> =
      Stream.of(
          "race-if-guard.c",
          "race-for-test.c",
          "race-initializer.c",
          "race-return.c",
          "race-pointer.c",
          "race-third-thread.c",
        )
        .map { Arguments.of(it) }
  }

  @ParameterizedTest
  @MethodSource("targets")
  fun testTargetAtFullExpression(file: String, property: String) {
    val input = File(javaClass.getResource("/c/witness-target/$file")!!.path)
    val lines = input.readLines()
    val line = lines.indexOfFirst { "// target: " in it } + 1
    assertTrue(line > 0) { "$file marks no target" }
    val code = lines[line - 1].substringAfter("// target: ")
    val column = lines[line - 1].indexOf(code) + 1
    val params = targetParams(input, property)
    val temp = createTempDirectory()
    val output = runCatchingOutput(params + "--output-directory" + temp.absolutePathString())
    assertTrue(output.getVerdict().contains("Unsafe")) {
      "Expected Unsafe, got ${output.getVerdict()}"
    }

    val witness = temp.getWitness()
    val targets = witness.waypoints().filter { it.type == WaypointType.TARGET }
    assertEquals(1, targets.size) { "Expected exactly one target, got $targets" }
    assertEquals(line, targets[0].location.line)
    assertEquals(column, targets[0].location.column) {
      "The target must point at '$code' on line $line of $file"
    }
    // a validator would have to reach the target statement once per waypoint at its location
    val beforeTarget =
      witness.waypoints().zipWithNext().firstOrNull { it.second == targets[0] }?.first
    assertTrue(beforeTarget?.location != targets[0].location) {
      "$beforeTarget repeats the target location"
    }

    val validation =
      runCatchingOutput(
        params +
          "--output-directory" +
          createTempDirectory().absolutePathString() +
          "--witness" +
          witness.absolutePath
      )
    assertEquals(output.getVerdict(), validation.getVerdict())
  }

  /** A data race has one target per racing access; each is marked in the input. */
  @ParameterizedTest
  @MethodSource("races")
  fun testRaceTargetsAtFullExpressions(file: String) {
    val input = File(javaClass.getResource("/c/witness-target/$file")!!.path)
    val marked =
      input
        .readLines()
        .withIndex()
        .filter { "// target: " in it.value }
        .map { (i, line) -> Pair(i + 1, line.indexOf(line.substringAfter("// target: ")) + 1) }
        .toSet()
    assertEquals(2, marked.size) { "$file must mark both racing accesses" }
    val params = targetParams(input, "no-data-race")
    val temp = createTempDirectory()
    val output = runCatchingOutput(params + "--output-directory" + temp.absolutePathString())
    assertTrue(output.getVerdict().contains("Unsafe")) {
      "Expected Unsafe, got ${output.getVerdict()}"
    }

    val witness = temp.getWitness()
    val targets =
      witness
        .waypoints()
        .filter { it.type == WaypointType.TARGET }
        .map { Pair(it.location.line, it.location.column) }
        .toSet()
    assertEquals(marked, targets) { "The targets must point at the racing accesses of $file" }

    val validation =
      runCatchingOutput(
        params +
          "--output-directory" +
          createTempDirectory().absolutePathString() +
          "--witness" +
          witness.absolutePath
      )
    assertEquals(output.getVerdict(), validation.getVerdict())
  }

  @Test
  fun testThreadRegistrationAtClosingParenthesis() {
    val input = File(javaClass.getResource("/c/witness-validation/concurrent-unreach.i")!!.path)
    val temp = createTempDirectory()
    val output =
      runCatchingOutput(
        arrayOf(
          "--input-type",
          "C",
          "--input",
          input.path,
          "--stacktrace",
          "--domain",
          "EXPL",
          "--output-directory",
          temp.absolutePathString(),
          "--svcomp",
          "--backend",
          "CEGAR",
          "--search",
          "DFS",
          "--por",
          "SPOR",
        )
      )
    assertTrue(output.getVerdict().contains("Unsafe")) {
      "Expected Unsafe, got ${output.getVerdict()}"
    }

    val registrations =
      temp.getWitness().waypoints().filter { it.type == WaypointType.FUNCTION_ENTER }
    assertTrue(registrations.isNotEmpty()) { "Expected a thread-registering function_enter" }
    for (registration in registrations) {
      val source = input.readLines()[registration.location.line - 1]
      assertTrue("pthread_create" in source) { "function_enter is not on a pthread_create line" }
      assertEquals(source.lastIndexOf(')') + 1, registration.location.column) {
        "function_enter must point at the closing parenthesis of: $source"
      }
    }
  }

  /** The trace of a NaN counterexample is feasible, so the nondet result keeps its waypoint. */
  @Test
  fun testNanFunctionReturn() {
    val input = File(javaClass.getResource("/c/witness-target/nan-return.c")!!.path)
    val temp = createTempDirectory()
    val output =
      runCatchingOutput(
        arrayOf(
          "--input-type",
          "C",
          "--input",
          input.path,
          "--stacktrace",
          "--output-directory",
          temp.absolutePathString(),
          "--svcomp",
          "--backend",
          "BOUNDED",
        )
      )
    assertTrue(output.getVerdict().contains("Unsafe")) {
      "Expected Unsafe, got ${output.getVerdict()}"
    }

    val returns = temp.getWitness().waypoints().filter { it.type == WaypointType.FUNCTION_RETURN }
    assertEquals(listOf("\\result != \\result"), returns.map { it.constraint?.value })
  }

  private fun targetParams(input: File, property: String): Array<String> =
    arrayOf(
      "--input-type",
      "C",
      "--input",
      input.path,
      "--property",
      javaClass.getResource("/c/witness-target/prop/$property.prp")!!.path,
      "--stacktrace",
      "--svcomp",
      "--backend",
      "CEGAR",
      "--domain",
      "PRED_CART",
      "--search",
      "DFS",
    )

  private fun File.waypoints(): List<WaypointContent> =
    WitnessYamlConfig.decodeFromString<List<YamlWitness>>(readText())
      .flatMap { it.content }
      .mapNotNull { it.segment }
      .flatten()
      .map { it.waypoint }

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

  private fun Path.getWitness(): File {
    val witnesses = toFile().listFiles().filter { it.name.startsWith("witness") }
    assertEquals(1, witnesses.size) { "$this does not contain exactly one witness ($witnesses)" }
    return witnesses[0]
  }

  private fun String.getVerdict(): String =
    (split(System.lineSeparator()).lastOrNull { "SafetyResult" in it } ?: "unsolved").replace(
      Regex(" Trace length: \\d+"),
      "",
    )
}
