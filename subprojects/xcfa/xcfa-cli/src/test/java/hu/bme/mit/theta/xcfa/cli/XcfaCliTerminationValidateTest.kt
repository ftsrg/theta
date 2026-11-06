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

import hu.bme.mit.theta.solver.smtlib.testing.SolverInstallations
import hu.bme.mit.theta.xcfa.cli.XcfaCli.Companion.main
import hu.bme.mit.theta.xcfa.cli.params.ErrorCodeException
import java.io.BufferedOutputStream
import java.io.FileOutputStream
import java.io.PrintStream
import java.util.stream.Stream
import kotlin.io.path.absolutePathString
import kotlin.io.path.createTempDirectory
import kotlin.io.path.readText
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertNotEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.BeforeAll
import org.junit.jupiter.api.Test
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.MethodSource

/**
 * Validation of termination correctness witnesses: their invariants are checked in the
 * liveness-to-safety reduction. A rejected witness gives Unsafe, as for correctness witnesses of
 * other properties; one that cannot be checked gives no verdict.
 */
class XcfaCliTerminationValidateTest {
  companion object {

    private val solvers = listOf("z3:4.13.0", "cvc5:1.0.8", "mathsat:5.6.10")

    private const val SAFE = "Safe"
    private const val UNSAFE = "Unsafe"
    private val VERDICT = Regex("""\(SafetyResult (\w+)""")

    @BeforeAll
    @JvmStatic
    fun installSolvers() {
      solvers.forEach(SolverInstallations::installOrSkip)
    }

    @JvmStatic
    fun validWitnesses(): Stream<Arguments> =
      Stream.of(
        Arguments.of("count-down.c", "count-down.loop.yml"),
        Arguments.of("count-down.c", "count-down.body.yml"),
        Arguments.of("bounded-count-down.c", "bounded-count-down.state.yml"),
      )

    @JvmStatic
    fun invalidWitnesses(): Stream<Arguments> =
      Stream.of(
        Arguments.of("count-down.c", "count-down.wrong-direction.yml"),
        Arguments.of("bounded-count-down.c", "bounded-count-down.wrong-state.yml"),
        Arguments.of("stay-positive.c", "stay-positive.yml"),
        // terminates only by signed overflow, which the bitvector model wraps around
        Arguments.of("count-up.c", "count-up.yml"),
      )

    @JvmStatic
    fun uncheckableWitnesses(): Stream<Arguments> =
      Stream.of(
        Arguments.of("count-down.c", "count-down.last-prev.yml", listOf<String>()),
        Arguments.of("count-down.c", "count-down.no-statement.yml", listOf<String>()),
        // infinitely many states: a state need not repeat in an infinite run
        Arguments.of("count-up.c", "count-up.yml", listOf("--arithmetic", "integer")),
        Arguments.of("count-down.c", "count-down.loop.yml", listOf("--backend", "MDD")),
      )
  }

  /** Without its transition invariant, k-induction cannot prove that count-down.c terminates. */
  @ParameterizedTest
  @MethodSource("validWitnesses")
  fun testValidWitness(program: String, witness: String) {
    assertEquals(SAFE, validate(program, witness))
  }

  @ParameterizedTest
  @MethodSource("invalidWitnesses")
  fun testInvalidWitness(program: String, witness: String) {
    assertEquals(UNSAFE, validate(program, witness))
  }

  @ParameterizedTest
  @MethodSource("uncheckableWitnesses")
  fun testUncheckableWitness(program: String, witness: String, extraArgs: List<String>) {
    // a backend that cannot check the witness throws while it is built
    val verdict = runCatching { validate(program, witness, extraArgs) }.getOrDefault("unsolved")
    assertNotEquals(SAFE, verdict)
  }

  @Test
  fun testPortfolio() {
    val portfolio = listOf("--backend", "PORTFOLIO", "--portfolio", "TERMINATION")
    assertEquals(SAFE, validate("count-down.c", "count-down.loop.yml", portfolio))
    assertEquals(UNSAFE, validate("count-down.c", "count-down.wrong-direction.yml", portfolio))
  }

  /** Theta's own transition invariants are confirmed by Theta. */
  @Test
  fun testRoundTrip() {
    val output = createTempDirectory()
    val verification =
      run(listOf("--backend", "IMC") + task("bounded-count-down.c") + outputTo(output.toString()))
    assertEquals(SAFE, verification)
    val witness = output.resolve("witness.yml")
    assertTrue("transition_invariant" in witness.readText())

    val validation =
      run(
        listOf("--backend", "KIND", "--witness", witness.absolutePathString()) +
          task("bounded-count-down.c") +
          outputTo(createTempDirectory().toString())
      )
    assertEquals(SAFE, validation)
  }

  private fun validate(
    program: String,
    witness: String,
    extraArgs: List<String> = listOf(),
  ): String {
    val backend = if ("--backend" in extraArgs) listOf() else listOf("--backend", "KIND")
    return run(
      backend +
        extraArgs +
        task(program) +
        listOf("--witness", resource("/c/termination/witnesses/$witness")) +
        outputTo(createTempDirectory().toString())
    )
  }

  private fun task(program: String) =
    listOf(
      "--input-type",
      "C",
      "--input",
      resource("/c/termination/$program"),
      "--property",
      resource("/c/termination/prop/termination.prp"),
      "--svcomp",
      "--debug",
      "--stacktrace",
    )

  private fun outputTo(dir: String) = listOf("--output-directory", dir)

  private fun resource(path: String) = javaClass.getResource(path)!!.path

  /** The last verdict printed by the run, or "unsolved" if it stopped on an error. */
  private fun run(params: List<String>): String {
    val output = createTempDirectory().resolve("output").toFile()
    PrintStream(BufferedOutputStream(FileOutputStream(output)), true).use { stream ->
      val out = System.out
      val err = System.err
      System.setOut(stream)
      System.setErr(stream)
      try {
        main(params.toTypedArray())
      } catch (_: ErrorCodeException) {} catch (e: IllegalStateException) {
        if (e.message != "Done debugging") throw e
      } finally {
        System.setOut(out)
        System.setErr(err)
        print(output.readText())
      }
    }
    return VERDICT.findAll(output.readText()).lastOrNull()?.groupValues?.get(1) ?: "unsolved"
  }
}
