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

class XcfaCliDssTest {

  companion object {

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

    private val randomCheckerBackendCombinations: List<String> =
      Random(20260824).let { rnd ->
        val allBackends = DssCheckerBackend.values()
        List(5) {
          List(rnd.nextInt(2, 5)) { allBackends[rnd.nextInt(allBackends.size)] }.joinToString(",")
        }
      }

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

  @Test
  fun `--dss-decomposition MIN_CUT_ACYCLIC runs to completion on a loop`() {
    main(
      arrayOf(
        "--backend",
        "DSS",
        "--dss-decomposition",
        "MIN_CUT_ACYCLIC",
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
  fun `--dss-reset-precision parses and runs to completion`(input: String) {
    main(
      arrayOf(
        "--backend",
        "DSS",
        "--dss-decomposition",
        "MERGE",
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
  fun `--dss-checker-selection PRIORITY parses and runs to completion`(input: String) {
    main(
      arrayOf(
        "--backend",
        "DSS",
        "--dss-checker-backends",
        "CEGAR_PRED_CART,KIND",
        "--dss-checker-selection",
        "PRIORITY",
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

  @ParameterizedTest
  @ValueSource(strings = ["SEQUENTIAL", "PROCESS"])
  fun `a SAFE run writes location invariants that Theta validates`(executor: String) {
    val witness = dssWitness("loop", executor)
    assertTrue(witness.contains("entry_type: 'invariant_set'")) { witness }
    assertTrue(witness.contains("location_invariant")) { witness }
    assertTrue(verdictWithWitness("loop", witness).contains("SafetyResult Safe"))
  }

  @ParameterizedTest
  @ValueSource(strings = ["SEQUENTIAL", "PROCESS"])
  fun `an UNSAFE run writes a stitched violation witness that Theta validates`(executor: String) {
    val witness = dssWitness("loop_unsafe", executor)
    assertTrue(witness.contains("entry_type: 'violation_sequence'")) { witness }
    assertTrue(witness.contains("\\result == 3")) { witness }
    assertTrue(witness.contains("type: 'target'")) { witness }
    assertTrue(verdictWithWitness("loop_unsafe", witness).contains("SafetyResult Unsafe"))
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
