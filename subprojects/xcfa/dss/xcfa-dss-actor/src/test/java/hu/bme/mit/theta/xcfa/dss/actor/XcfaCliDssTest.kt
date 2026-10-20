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
package hu.bme.mit.theta.xcfa.dss.actor

import hu.bme.mit.theta.xcfa.cli.XcfaCli.Companion.main
import hu.bme.mit.theta.xcfa.cli.params.DssCheckerBackend
import hu.bme.mit.theta.xcfa.cli.params.DssDecomposition
import java.io.BufferedOutputStream
import java.io.FileOutputStream
import java.io.PrintStream
import java.util.stream.Stream
import kotlin.io.path.absolutePathString
import kotlin.io.path.createTempDirectory
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.EnumSource
import org.junit.jupiter.params.provider.MethodSource
import org.junit.jupiter.params.provider.ValueSource

class XcfaCliDssTest {

  companion object {

    @JvmStatic
    fun decompositions(): Stream<Arguments> =
      DssDecomposition.entries
        .flatMap { d -> listOf("loop", "loop_unsafe").map { Arguments.of(d.name, it) } }
        .stream()

    @JvmStatic
    fun options(): Stream<Arguments> =
      listOf(
          listOf("--dss-executor", "CONCURRENT"),
          listOf("--output", "ALL"),
          listOf("--dss-reset-precision"),
          listOf("--dss-reuse-block-precision"),
          listOf("--dss-global-predicate-pool", "false"),
          listOf(
            "--dss-checker-backends",
            "CEGAR_PRED_CART,KIND",
            "--dss-checker-selection",
            "PRIORITY",
          ),
          listOf(
            "--dss-checker-backends",
            "CEGAR_PRED_CART,KIND",
            "--dss-checker-selection",
            "FASTEST",
          ),
          listOf(
            "--dss-checker-backends",
            "CEGAR_PRED_CART,BMC",
            "--dss-checker-selection",
            "ROUND_ROBIN",
          ),
        )
        .flatMap { o -> listOf("safe", "unsafe").map { Arguments.of(o, it) } }
        .stream()
  }

  private fun expected(program: String) =
    if (program.endsWith("unsafe")) "SafetyResult Unsafe" else "SafetyResult Safe"

  @ParameterizedTest(name = "{0} on {1}")
  @MethodSource("decompositions")
  fun `every decomposition gives the right verdict`(decomposition: String, program: String) {
    assertTrue(
      dssVerdict(program, "--dss-decomposition", decomposition).contains(expected(program))
    )
  }

  @ParameterizedTest(name = "{0} on {1}")
  @MethodSource("options")
  fun `every option keeps the verdict`(options: List<String>, program: String) {
    assertTrue(dssVerdict(program, *options.toTypedArray()).contains(expected(program)))
  }

  @ParameterizedTest
  @EnumSource(DssCheckerBackend::class)
  fun `every checker backend finds the violation`(backend: DssCheckerBackend) {
    assertTrue(dssVerdict("unsafe", "--dss-checker-backends", backend.name).contains("Unsafe"))
  }

  @Test
  fun `a backend outside the DSS-compatible subset is rejected`() {
    val (output, thrown) = runDss("safe", "--dss-checker-backends", "OC")
    assertTrue(thrown != null && "OC" in output) { output }
  }

  @Test
  fun `properties a pass reduces to error-location reachability are checked`() {
    assertTrue(
      dssVerdict("overflow_unsafe", property = "no-overflow").contains("SafetyResult Unsafe")
    )
    assertTrue(
      dssVerdict("assert_unsafe", property = "no-assertion-violation")
        .contains("SafetyResult Unsafe")
    )
  }

  @Test
  fun `termination is rejected`() {
    val (output, thrown) = runDss("safe", property = "termination")
    assertTrue(thrown != null && "not TERMINATION" in output) { output }
  }

  @ParameterizedTest
  @ValueSource(strings = ["safe", "unsafe"])
  fun `--loglevel INFO prints exactly one SafetyResult line, the DSS verdict`(program: String) {
    val (output, thrown) = runDss(program, "--loglevel", "INFO", debug = false)
    assertEquals(null, thrown)
    val resultLines = output.lines().filter { it.contains("SafetyResult") }
    assertEquals(1, resultLines.size) { "$resultLines" }
    assertTrue(resultLines.single().contains(expected(program))) { resultLines.single() }
  }

  @Test
  fun `a SAFE run writes location invariants that Theta validates`() {
    val witness = dssWitness("loop", "SEQUENTIAL")
    assertTrue(witness.contains("entry_type: 'invariant_set'")) { witness }
    assertTrue(witness.contains("location_invariant")) { witness }
    assertTrue(verdictWithWitness("loop", witness).contains("SafetyResult Safe"))
  }

  /** Each worker process only knows its own blocks, so the trace is stitched from all of them. */
  @Test
  fun `an UNSAFE run of the process executor writes a stitched violation witness`() {
    val witness = dssWitness("loop_unsafe", "PROCESS")
    assertTrue(witness.contains("entry_type: 'violation_sequence'")) { witness }
    assertTrue(witness.contains("\\result == 3")) { witness }
    assertTrue(witness.contains("type: 'target'")) { witness }
    assertTrue(verdictWithWitness("loop_unsafe", witness).contains("SafetyResult Unsafe"))
  }

  /** The verdict line of a DSS run on [program] against `<property>.prp`. */
  private fun dssVerdict(
    program: String,
    vararg options: String,
    property: String = "unreach-call",
  ): String {
    val (output, thrown) = runDss(program, *options, property = property)
    if (thrown != null) throw AssertionError(output, thrown)
    return output.lines().lastOrNull { it.contains("SafetyResult") }.orEmpty()
  }

  /** The output of a DSS run on [program] against `<property>.prp`, and what it threw. */
  private fun runDss(
    program: String,
    vararg options: String,
    property: String = "unreach-call",
    debug: Boolean = true,
  ): Pair<String, Throwable?> {
    val temp = createTempDirectory()
    val captured = temp.resolve("stdout_stderr").toFile()
    var thrown: Throwable? = null
    try {
      PrintStream(BufferedOutputStream(FileOutputStream(captured)), true).use { ps ->
        val savedOut = System.out
        val savedErr = System.err
        System.setOut(ps)
        System.setErr(ps)
        try {
          main(
            arrayOf(
              "--backend",
              "DSS",
              *options,
              "--property",
              javaClass.getResource("/c/dss/$property.prp")!!.path,
              "--output-directory",
              temp.absolutePathString(),
              "--input",
              javaClass.getResource("/c/dss/$program.c")!!.path,
              "--stacktrace",
              *(if (debug) arrayOf("--debug") else emptyArray()),
            )
          )
        } catch (e: Exception) {
          thrown = e
        } finally {
          System.setOut(savedOut)
          System.setErr(savedErr)
        }
      }
      return captured.readText() to thrown
    } finally {
      temp.toFile().deleteRecursively()
    }
  }

  /** The SV-COMP witness of a DSS run on [program] with emergent27's settings. */
  private fun dssWitness(program: String, executor: String): String {
    val temp = createTempDirectory()
    try {
      main(
        arrayOf(
          "--svcomp",
          "--backend",
          "DSS",
          "--dss-executor",
          executor,
          "--dss-decomposition",
          "MIN_CUT_ABSORB_SELF_LOOPS",
          "--dss-checker-backends",
          "CEGAR_PRED_CART,KIND",
          "--dss-checker-selection",
          "PRIORITY",
          "--property",
          javaClass.getResource("/c/dss/unreach-call.prp")!!.path,
          "--output-directory",
          temp.absolutePathString(),
          "--input",
          javaClass.getResource("/c/dss/$program.c")!!.path,
          "--stacktrace",
        )
      )
      return temp.resolve("witness.yml").toFile().readText()
    } finally {
      temp.toFile().deleteRecursively()
    }
  }

  /** The verdict line of the STABLE portfolio on [program] restricted by [witness]. */
  private fun verdictWithWitness(program: String, witness: String): String {
    val temp = createTempDirectory()
    val witnessFile = temp.resolve("witness.yml").toFile().apply { writeText(witness) }
    val captured = temp.resolve("stdout_stderr").toFile()
    try {
      PrintStream(BufferedOutputStream(FileOutputStream(captured)), true).use { ps ->
        val savedOut = System.out
        System.setOut(ps)
        try {
          main(
            arrayOf(
              "--svcomp",
              "--portfolio",
              "STABLE",
              "--property",
              javaClass.getResource("/c/dss/unreach-call.prp")!!.path,
              "--witness",
              witnessFile.absolutePath,
              "--output-directory",
              temp.resolve("validation").absolutePathString(),
              "--input",
              javaClass.getResource("/c/dss/$program.c")!!.path,
            )
          )
        } finally {
          System.setOut(savedOut)
        }
      }
      return captured.readLines().lastOrNull { it.contains("SafetyResult") }.orEmpty()
    } finally {
      temp.toFile().deleteRecursively()
    }
  }
}
