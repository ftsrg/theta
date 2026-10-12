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
 * End-to-end tests for `--backend DSS` (build-order step 8's CLI integration,
 * [hu.bme.mit.theta.xcfa.cli.checkers.getDssChecker]) - the actual new surface here is the CLI
 * wiring itself (flag parsing, backend dispatch, result/witness reporting), not DSS's own
 * decomposition/analysis/actor logic, which already has 104 tests across the `xcfa-dss-*` modules.
 */
class XcfaCliDssTest {

  companion object {

    // The full decomposition x executor grid, as data - decompositionAndExecutor() (below) exposes
    // it as-is for the existing single-axis tests;
    // randomCheckerBackendsAndDecompositionAndExecutor()
    // crosses it against every random backend combination, so both method sources stay in sync with
    // one definition instead of two copies of the same sixteen pairs drifting apart.
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

    // Fixed-seed pseudo-randomness, mirroring this codebase's own convention for reproducible
    // randomized coverage (see XcfaExplAnalysisTest/XcfaPredAnalysisTest's own `Random(seed)`
    // driving XcfaDporLts) - five independent, genuinely random-looking subset/order/repeat-count
    // draws from the full DssCheckerBackend range (2 to 4 entries each, drawn with replacement, so
    // repeats like "BMC,BMC" are possible within one combination), all five computed once from a
    // single seeded Random up front so a run is fully reproducible end to end - but none
    // hand-picked/curated the way checkerBackendLists()'s entries are, and a different seed would
    // exercise five different combinations without anyone having to think them up by hand.
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
    // Each of the three CEGAR domains (PRED_CART - the original default and only option before
    // this, PRED_BOOL, PRED_SPLIT) individually, a list mixing all three, the bounded-model-
    // checking-family entries (BMC/KIND/IMC/KINDIMC/BOUNDED, which go through adaptBoundedChecker),
    // and a list mixing CEGAR and bounded are all covered, confirming DssCheckerRoster genuinely
    // receives a heterogeneous roster and runs it to completion regardless of which Domain/backend
    // built each entry. Correctness of checker *selection* itself (round-robin balance, a custom
    // strategy being consulted) is already proven at the pure DssCheckerRoster level
    // (DssCheckerRosterTest) and the solver-backed PredicateBlockBehaviorTest; this test's own job,
    // like every other test in this file, is just the CLI wiring.
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
    // Crosses all five randomCheckerBackendCombinations (each a heterogeneous, possibly-repeated,
    // possibly-CEGAR+bounded-mixed roster - see that val's own doc) against the full decomposition
    // x
    // executor grid `every --dss-decomposition and --dss-executor combination parses and runs`
    // already covers with the default single-CEGAR roster - 30 combinations no fixed, hand-picked
    // test above exercises, since checkerBackendLists()'s own tests all run with the default
    // decomposition/executor.
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
    // DssCheckerBackend deliberately excludes backends whose checker doesn't produce DSS's
    // required LocationInvariants/Trace proof shape (OC/CHC/PORTFOLIO/...), or that do but simply
    // aren't wired in yet (IC3/MDD). JCommander's own enum parsing is what actually rejects an
    // out-of-subset name like OC, the same way any other misspelled/unsupported enum value on this
    // CLI already does - this is CLI-wiring coverage that the restriction is real, not a new
    // validation path of DSS's own.
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
    // DSS's UNSAFE verdict carries no concrete counterexample trace (doc/DSS.md's Known
    // Limitations - packVcond/unpackVcond aren't implemented) - this is exactly the case that
    // exposed a latent unchecked-cast crash in VerificationLogging.kt's trace-writing code, fixed
    // alongside this backend. --output ALL is the default WitnessLevel, so this also doubles as a
    // regression test for that fix without needing to force any extra flags.
    //
    // Reaching the assertion below at all is the actual regression guard: before the fix, this
    // threw a ClassCastException (EmptyCex is not a Trace) from inside the witness-writing block,
    // caught only by the generic "Could not output files" catch-all. There genuinely is no
    // witness.graphml/witness.yml afterward either way - GraphmlWitnessWriter/YamlWitnessWriter
    // both decline to write anything meaningful without a concrete trace, which is correct, not a
    // bug (see the same Known Limitation - DSS cannot yet produce violation witnesses).
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
