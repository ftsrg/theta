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
import hu.bme.mit.theta.xcfa.cli.params.DssCheckerBackend
import java.io.BufferedOutputStream
import java.io.FileOutputStream
import java.io.PrintStream
import java.util.stream.Stream
import kotlin.io.path.absolutePathString
import kotlin.io.path.createTempDirectory
import kotlin.io.path.exists
import kotlin.random.Random
import org.junit.jupiter.api.Assertions.assertThrows
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.MethodSource
import org.junit.jupiter.params.provider.ValueSource

/**
 * End-to-end tests for `--backend DSS` ([hu.bme.mit.theta.xcfa.cli.checkers.getDssChecker]),
 * covering the CLI wiring itself; DSS's own logic is tested in the `xcfa-dss-*` modules.
 */
class XcfaCliDssTest {

  companion object {

    // The decomposition x executor grid, defined once and shared by decompositionAndExecutor() and
    // randomCheckerBackendsAndDecompositionAndExecutor() so the two can't drift apart.
    private val decompositionExecutorPairs: List<Pair<String, String>> =
      listOf(
        "LINEAR" to "CONCURRENT",
        "LINEAR" to "SEQUENTIAL",
        "MERGE" to "CONCURRENT",
        "MERGE" to "SEQUENTIAL",
        "MERGE_ABSORB_SELF_LOOPS" to "CONCURRENT",
        "MERGE_ABSORB_SELF_LOOPS" to "SEQUENTIAL",
        "MERGE_ACYCLIC" to "CONCURRENT",
        "MERGE_ACYCLIC" to "SEQUENTIAL",
        "MIN_CUT" to "CONCURRENT",
        "MIN_CUT" to "SEQUENTIAL",
        "MIN_CUT_ABSORB_SELF_LOOPS" to "CONCURRENT",
        "MIN_CUT_ABSORB_SELF_LOOPS" to "SEQUENTIAL",
        "MIN_CUT_ACYCLIC" to "CONCURRENT",
        "MIN_CUT_ACYCLIC" to "SEQUENTIAL",
        "NONE" to "CONCURRENT",
        "NONE" to "SEQUENTIAL",
      )

    @JvmStatic
    fun decompositionAndExecutor(): Stream<Arguments> =
      decompositionExecutorPairs.stream().map { (decomposition, executor) ->
        Arguments.of(decomposition, executor)
      }

    @JvmStatic
    fun checkerBackendLists(): Stream<Arguments> =
      Stream.of(
        Arguments.of("CEGAR_PRED_CART"),
        Arguments.of("CEGAR_PRED_BOOL"),
        Arguments.of("CEGAR_PRED_SPLIT"),
        Arguments.of("BMC"),
        Arguments.of("KIND"),
        Arguments.of("IMC"),
        Arguments.of("KINDIMC"),
        Arguments.of("BOUNDED"),
        Arguments.of("CEGAR_PRED_CART,CEGAR_PRED_BOOL,CEGAR_PRED_SPLIT"),
        Arguments.of("CEGAR_PRED_CART,BMC,IMC"),
        Arguments.of("CEGAR_PRED_CART,CEGAR_PRED_CART,BMC"),
      )

    // Five random 2-4 entry DssCheckerBackend combinations (with repeats), drawn once from a fixed
    // seed: reproducible, yet not hand-picked like checkerBackendLists().
    private val randomCheckerBackendCombinations: List<String> =
      Random(20260824).let { rnd ->
        val allBackends = DssCheckerBackend.values()
        List(5) {
          List(rnd.nextInt(2, 5)) { allBackends[rnd.nextInt(allBackends.size)] }.joinToString(",")
        }
      }

    // The cross product: every one of the five randomCheckerBackendCombinations against every one
    // of the sixteen decompositionExecutorPairs - 80 argument sets, so each random combination
    // really
    // does get "run on every testcase," not just the default decomposition/executor.
    @JvmStatic
    fun randomCheckerBackendsAndDecompositionAndExecutor(): Stream<Arguments> =
      randomCheckerBackendCombinations
        .flatMap { backends ->
          decompositionExecutorPairs.map { (decomposition, executor) ->
            Arguments.of(backends, decomposition, executor)
          }
        }
        .stream()
  }

  @ParameterizedTest
  @ValueSource(strings = ["2", "3"])
  fun `--dss-decomposition MIN_CUT_ACYCLIC with --dss-cut-block-count runs to completion on a loop`(
    blocks: String
  ) {
    main(
      arrayOf(
        "--backend",
        "DSS",
        "--dss-decomposition",
        "MIN_CUT_ACYCLIC",
        "--dss-cut-block-count",
        blocks,
        "--input-type",
        "C",
        "--input",
        javaClass.getResource("/c/dss/loop.c")!!.path,
        "--stacktrace",
        "--debug",
      )
    )
  }

  @Test
  fun `--backend DSS runs to completion on a SAFE program`() {
    main(
      arrayOf(
        "--backend",
        "DSS",
        "--input-type",
        "C",
        "--input",
        javaClass.getResource("/c/dss/safe.c")!!.path,
        "--stacktrace",
        "--debug",
      )
    )
  }

  @Test
  fun `--backend DSS runs to completion on an UNSAFE program`() {
    main(
      arrayOf(
        "--backend",
        "DSS",
        "--input-type",
        "C",
        "--input",
        javaClass.getResource("/c/dss/unsafe.c")!!.path,
        "--stacktrace",
        "--debug",
      )
    )
  }

  @ParameterizedTest
  @MethodSource("decompositionAndExecutor")
  fun `every --dss-decomposition and --dss-executor combination parses and runs on a SAFE program`(
    decomposition: String,
    executor: String,
  ) {
    main(
      arrayOf(
        "--backend",
        "DSS",
        "--dss-decomposition",
        decomposition,
        "--dss-executor",
        executor,
        "--input-type",
        "C",
        "--input",
        javaClass.getResource("/c/dss/safe.c")!!.path,
        "--stacktrace",
        "--debug",
      )
    )
  }

  @ParameterizedTest
  @MethodSource("decompositionAndExecutor")
  fun `every --dss-decomposition and --dss-executor combination parses and runs on an UNSAFE program`(
    decomposition: String,
    executor: String,
  ) {
    main(
      arrayOf(
        "--backend",
        "DSS",
        "--dss-decomposition",
        decomposition,
        "--dss-executor",
        executor,
        "--input-type",
        "C",
        "--input",
        javaClass.getResource("/c/dss/unsafe.c")!!.path,
        "--stacktrace",
        "--debug",
      )
    )
  }

  @ParameterizedTest
  @ValueSource(strings = ["/c/dss/safe.c", "/c/dss/unsafe.c"])
  fun `the CPAchecker merge and precision options parse and run to completion`(input: String) {
    main(
      arrayOf(
        "--backend",
        "DSS",
        "--dss-decomposition",
        "MERGE",
        "--dss-target-block-count",
        "1",
        "--dss-largest-horizontal-merge",
        "1",
        "--dss-allow-single-block-decomposition",
        "--dss-reset-precision",
        "--input-type",
        "C",
        "--input",
        javaClass.getResource(input)!!.path,
        "--stacktrace",
        "--debug",
      )
    )
  }

  @ParameterizedTest
  @ValueSource(strings = ["/c/dss/safe.c", "/c/dss/unsafe.c"])
  fun `--dss-reuse-block-precision parses and runs to completion`(input: String) {
    // Which precision each run starts with is covered by xcfa-dss-actor's ReuseBlockPrecisionTest.
    main(
      arrayOf(
        "--backend",
        "DSS",
        "--dss-reuse-block-precision",
        "--input-type",
        "C",
        "--input",
        javaClass.getResource(input)!!.path,
        "--stacktrace",
        "--debug",
      )
    )
  }

  @ParameterizedTest
  @ValueSource(strings = ["/c/dss/safe.c", "/c/dss/unsafe.c"])
  fun `--dss-checker-selection PRIORITY with fallback parses and runs to completion`(
    input: String
  ) {
    // Which checker each try uses is covered by xcfa-dss-actor's CheckerFallbackTest.
    main(
      arrayOf(
        "--backend",
        "DSS",
        "--dss-checker-backends",
        "CEGAR_PRED_CART,KIND",
        "--dss-checker-selection",
        "PRIORITY",
        "--dss-checker-fallback",
        "--input-type",
        "C",
        "--input",
        javaClass.getResource(input)!!.path,
        "--stacktrace",
        "--debug",
      )
    )
  }

  @ParameterizedTest
  @ValueSource(strings = ["/c/dss/safe.c", "/c/dss/unsafe.c"])
  fun `--dss-checker-selection FASTEST parses and runs to completion`(input: String) {
    // Which checker each try uses is covered by xcfa-dss-actor's CheckerFallbackTest.
    main(
      arrayOf(
        "--backend",
        "DSS",
        "--dss-checker-backends",
        "CEGAR_PRED_CART,KIND",
        "--dss-checker-selection",
        "FASTEST",
        "--input-type",
        "C",
        "--input",
        javaClass.getResource(input)!!.path,
        "--stacktrace",
        "--debug",
      )
    )
  }

  @Test
  fun `--dss-global-predicate-pool false parses and runs to completion`() {
    // Verdict correctness without the pool is covered at the xcfa-dss-actor level - see
    // PredicateBlockBehaviorTest's `without the global predicate pool, violation conditions still
    // refute the spurious error`. This test's own job, matching every other test in this file, is
    // just the CLI wiring: does the flag parse and flow through to a completed run.
    main(
      arrayOf(
        "--backend",
        "DSS",
        "--dss-global-predicate-pool",
        "false",
        "--input-type",
        "C",
        "--input",
        javaClass.getResource("/c/dss/safe.c")!!.path,
        "--stacktrace",
        "--debug",
      )
    )
  }

  @ParameterizedTest
  @MethodSource("checkerBackendLists")
  fun `--dss-checker-backends builds and runs to completion on a SAFE program`(backends: String) {
    // Single CEGAR domains, mixed CEGAR, bounded and CEGAR+bounded rosters all run to completion;
    // checker selection itself is tested in DssCheckerRosterTest/PredicateBlockBehaviorTest.
    main(
      arrayOf(
        "--backend",
        "DSS",
        "--dss-checker-backends",
        backends,
        "--input-type",
        "C",
        "--input",
        javaClass.getResource("/c/dss/safe.c")!!.path,
        "--stacktrace",
        "--debug",
      )
    )
  }

  @Test
  fun `--dss-checker-backends CEGAR_PRED_CART,CEGAR_PRED_BOOL,BMC,KIND builds and runs to completion on an UNSAFE program`() {
    main(
      arrayOf(
        "--backend",
        "DSS",
        "--dss-checker-backends",
        "CEGAR_PRED_CART,CEGAR_PRED_BOOL,BMC,KIND",
        "--input-type",
        "C",
        "--input",
        javaClass.getResource("/c/dss/unsafe.c")!!.path,
        "--stacktrace",
        "--debug",
      )
    )
  }

  @ParameterizedTest
  @MethodSource("randomCheckerBackendsAndDecompositionAndExecutor")
  fun `each of 5 random --dss-checker-backends combinations runs on every --dss-decomposition x --dss-executor combination on a SAFE program`(
    backends: String,
    decomposition: String,
    executor: String,
  ) {
    // Every random backend combination against the full decomposition x executor grid - 30
    // combinations the default-roster tests above never exercise.
    main(
      arrayOf(
        "--backend",
        "DSS",
        "--dss-decomposition",
        decomposition,
        "--dss-executor",
        executor,
        "--dss-checker-backends",
        backends,
        "--input-type",
        "C",
        "--input",
        javaClass.getResource("/c/dss/safe.c")!!.path,
        "--stacktrace",
        "--debug",
      )
    )
  }

  @ParameterizedTest
  @MethodSource("randomCheckerBackendsAndDecompositionAndExecutor")
  fun `each of 5 random --dss-checker-backends combinations runs on every --dss-decomposition x --dss-executor combination on an UNSAFE program`(
    backends: String,
    decomposition: String,
    executor: String,
  ) {
    main(
      arrayOf(
        "--backend",
        "DSS",
        "--dss-decomposition",
        decomposition,
        "--dss-executor",
        executor,
        "--dss-checker-backends",
        backends,
        "--input-type",
        "C",
        "--input",
        javaClass.getResource("/c/dss/unsafe.c")!!.path,
        "--stacktrace",
        "--debug",
      )
    )
  }

  @Test
  fun `--dss-checker-backends rejects a backend outside the DSS-compatible subset`() {
    // JCommander's enum parsing rejects backends outside DssCheckerBackend (e.g. OC); this covers
    // that CLI restriction, not a DSS validation path.
    val temp = createTempDirectory()
    val captured = temp.resolve("stdout_stderr").toFile()
    PrintStream(BufferedOutputStream(FileOutputStream(captured)), true).use { ps ->
      val savedOut = System.out
      val savedErr = System.err
      System.setOut(ps)
      System.setErr(ps)
      try {
        assertThrows(Exception::class.java) {
          main(
            arrayOf(
              "--backend",
              "DSS",
              "--dss-checker-backends",
              "OC",
              "--input-type",
              "C",
              "--input",
              javaClass.getResource("/c/dss/safe.c")!!.path,
              "--stacktrace",
              "--debug",
            )
          )
        }
      } finally {
        System.setOut(savedOut)
        System.setErr(savedErr)
      }
    }
    val output = captured.readText()
    assertTrue(output.contains("OC")) {
      "expected JCommander's own invalid-enum-value message to mention OC, got: $output"
    }
    temp.toFile().deleteRecursively()
  }

  @Test
  fun `--dss-checker-selection ROUND_ROBIN parses and runs to completion`() {
    // ROUND_ROBIN is currently the only DssCheckerSelectionMethod, so this is CLI-wiring coverage
    // only (the flag parses and is actually translated into a strategy DssCheckerRoster accepts) -
    // matching the file's convention that flag-wiring tests belong here, not in xcfa-dss-analysis.
    main(
      arrayOf(
        "--backend",
        "DSS",
        "--dss-checker-backends",
        "CEGAR_PRED_CART,BMC,KIND",
        "--dss-checker-selection",
        "ROUND_ROBIN",
        "--input-type",
        "C",
        "--input",
        javaClass.getResource("/c/dss/safe.c")!!.path,
        "--stacktrace",
        "--debug",
      )
    )
  }

  @Test
  fun `--backend DSS with --output ALL does not crash on witness writing for an UNSAFE (no-trace) verdict`() {
    // Regression test: DSS's UNSAFE verdict carries no trace (EmptyCex), which used to crash
    // VerificationLogging.kt's trace writing with a ClassCastException. No witness file is
    // expected either way, as DSS can't produce violation witnesses yet.
    val temp = createTempDirectory()
    main(
      arrayOf(
        "--output",
        "ALL",
        "--output-directory",
        temp.absolutePathString(),
        "--backend",
        "DSS",
        "--input-type",
        "C",
        "--input",
        javaClass.getResource("/c/dss/unsafe.c")!!.path,
        "--stacktrace",
        "--debug",
      )
    )
    assertTrue(temp.exists())
    temp.toFile().deleteRecursively()
  }

  @ParameterizedTest
  @ValueSource(strings = ["safe", "unsafe"])
  fun `--loglevel INFO prints exactly one SafetyResult line, the DSS verdict`(program: String) {
    // Every block analysis is an ordinary checker that logs its own SafetyResult; those must not
    // reach the output at INFO, or BenchExec's theta-xcfa tool-info (which takes the last
    // SafetyResult line) would score a crashing DSS run with a block's result.
    val temp = createTempDirectory()
    val captured = temp.resolve("stdout_stderr").toFile()
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
            "--input-type",
            "C",
            "--input",
            javaClass.getResource("/c/dss/$program.c")!!.path,
            "--stacktrace",
            "--loglevel",
            "INFO",
          )
        )
      } finally {
        System.setOut(savedOut)
        System.setErr(savedErr)
      }
    }
    val resultLines = captured.readLines().filter { it.contains("SafetyResult") }
    temp.toFile().deleteRecursively()
    assertTrue(resultLines.size == 1) { "expected one SafetyResult line, got: $resultLines" }
    val expected = if (program == "safe") "SafetyResult Safe" else "SafetyResult Unsafe"
    assertTrue(resultLines.single().contains(expected)) {
      "expected $expected, got: ${resultLines.single()}"
    }
  }
}
