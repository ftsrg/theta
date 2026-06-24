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

import hu.bme.mit.theta.common.OsHelper
import hu.bme.mit.theta.common.logging.ConsoleLogger
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.frontend.chc.ChcFrontend
import hu.bme.mit.theta.solver.smtlib.SmtLibSolverManager
import hu.bme.mit.theta.xcfa.cli.XcfaCli.Companion.main
import hu.bme.mit.theta.xcfa.witnesses.Format
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
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Assumptions
import org.junit.jupiter.api.BeforeAll
import org.junit.jupiter.api.Disabled
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.MethodSource

class XcfaCliValidateTest {
  companion object {

    private val SMTLIB_HOME: Path = SmtLibSolverManager.HOME
    private val solvers =
      listOf("z3:4.13.0", "eldarica:2.1", "golem:0.5.0", "mathsat:5.6.10", "cvc5:1.0.8")

    private fun installSolver(name: String) {
      try {
        SmtLibSolverManager.create(SMTLIB_HOME, ConsoleLogger(Logger.Level.DETAIL)).use {
          solverManager ->
          val solverVersion = SmtLibSolverManager.getSolverVersion(name)
          val solverName = SmtLibSolverManager.getSolverName(name)
          if (
            solverManager.managesSolver(name) &&
              !solverManager
                .getInstalledVersions(solverName)
                .contains(solverManager.getVersionString(solverName, solverVersion, false))
          ) {
            solverManager.install(solverName, solverVersion, solverVersion, null, false)
          }
        }
      } catch (e: Exception) {
        e.printStackTrace() // best effort
      }
    }

    @BeforeAll
    @JvmStatic
    fun installSolvers() {
      if (OsHelper.getOs().equals(OsHelper.OperatingSystem.LINUX)) {
        solvers.forEach(this::installSolver)
      }
    }

    @JvmStatic
    fun cFiles(): Stream<Arguments> {
      return Stream.of(
        Arguments.of("/c/litmustest/singlethread/00assignment.c", null),
        Arguments.of("/c/litmustest/singlethread/01cast.c", null),
        Arguments.of("/c/litmustest/singlethread/02types.c", null),
        Arguments.of("/c/litmustest/singlethread/03bitwise.c", null),
        Arguments.of("/c/litmustest/singlethread/04real.c", null),
        Arguments.of("/c/litmustest/singlethread/06arrays.c", null),
        Arguments.of("/c/litmustest/singlethread/07arrayinit.c", null),
        Arguments.of("/c/litmustest/singlethread/08vararray.c", null),
        Arguments.of("/c/litmustest/singlethread/13typedef.c", "--domain PRED_CART"),
        Arguments.of("/c/litmustest/singlethread/14ushort.c", null),
        Arguments.of("/c/litmustest/singlethread/15addition.c", null),
        Arguments.of("/c/litmustest/singlethread/16loop.c", null),
        Arguments.of("/c/litmustest/singlethread/18multithread.c", "--search DFS --por SPOR"),
        Arguments.of("/c/litmustest/singlethread/19dportest.c", "--search DFS --por SPOR"),
        Arguments.of("/c/litmustest/singlethread/20testinline.c", null),
        Arguments.of("/c/litmustest/singlethread/21namecollision.c", null),
        Arguments.of("/c/litmustest/singlethread/22nondet.c", null),
        Arguments.of("/c/litmustest/singlethread/23overflow.c", "--domain PRED_CART"),
        Arguments.of("/c/litmustest/singlethread/31structaccess.c", "--domain PRED_CART"),
        Arguments.of("/c/litmustest/singlethread/23overflow.c", "--property no-overflow.prp"),
      )
    }

    @JvmStatic
    fun singleThreadedCFiles(): Stream<Arguments> {
      return Stream.of(
        Arguments.of("/c/litmustest/singlethread/00assignment.c", null),
        Arguments.of("/c/litmustest/singlethread/01cast.c", null),
        Arguments.of("/c/litmustest/singlethread/02types.c", null),
        Arguments.of("/c/litmustest/singlethread/03bitwise.c", null),
        Arguments.of("/c/litmustest/singlethread/04real.c", null),
        Arguments.of("/c/litmustest/singlethread/13typedef.c", "--domain PRED_CART"),
        Arguments.of("/c/litmustest/singlethread/14ushort.c", null),
        Arguments.of("/c/litmustest/singlethread/15addition.c", null),
        Arguments.of("/c/litmustest/singlethread/20testinline.c", null),
        Arguments.of("/c/litmustest/singlethread/21namecollision.c", null),
        Arguments.of("/c/litmustest/singlethread/22nondet.c", null),
        Arguments.of("/c/litmustest/singlethread/23overflow.c", "--domain PRED_CART"),
        Arguments.of("/c/litmustest/singlethread/23overflow.c", "--property no-overflow.prp"),
      )
    }

    @JvmStatic
    fun finiteStateSpaceC(): Stream<Arguments> {
      return Stream.of(
        Arguments.of("/c/litmustest/singlethread/00assignment.c", null),
        Arguments.of("/c/litmustest/singlethread/13typedef.c", "--domain PRED_CART"),
        Arguments.of("/c/litmustest/singlethread/15addition.c", null),
        Arguments.of("/c/litmustest/singlethread/20testinline.c", null),
      )
    }

    @JvmStatic
    fun cFilesShort(): Stream<Arguments> {
      return Stream.of(
        Arguments.of("/c/litmustest/singlethread/00assignment.c", null),
        Arguments.of("/c/litmustest/singlethread/01cast.c", null),
        Arguments.of("/c/litmustest/singlethread/02types.c", null),
        Arguments.of("/c/litmustest/singlethread/03bitwise.c", null),
        Arguments.of("/c/litmustest/singlethread/04real.c", null),
      )
    }

    @JvmStatic
    fun cFilesShortInt(): Stream<Arguments> {
      return Stream.of(
        Arguments.of("/c/litmustest/singlethread/01cast.c", null),
        Arguments.of("/c/litmustest/singlethread/02types.c", null),
        Arguments.of("/c/litmustest/singlethread/20testinline.c", null),
        Arguments.of("/c/litmustest/singlethread/21namecollision.c", null),
        Arguments.of("/c/litmustest/singlethread/22nondet.c", null),
        Arguments.of("/c/litmustest/singlethread/23overflow.c", "--property no-overflow.prp"),
      )
    }

    @JvmStatic
    fun chcFiles(): Stream<Arguments> {
      return Stream.of(
        Arguments.of(
          "/chc/chc-LIA-Lin_000.smt2",
          ChcFrontend.ChcTransformation.FORWARD,
          "--domain PRED_CART",
        )
      )
    }

    @JvmStatic
    fun multithreadedWitnesses(): Stream<Arguments> {
      return Stream.of(
        // a valid concurrent (format 2.2, thread_id) witness is confirmed
        Arguments.of(
          "/c/witness-validation/concurrent-unreach.i",
          "/c/witness-validation/concurrent-unreach.witness.yml",
          null,
          "SafetyResult Unsafe",
        ),
        // a witness whose segment sequence is infeasible is refuted
        Arguments.of(
          "/c/witness-validation/concurrent-unreach.i",
          "/c/witness-validation/concurrent-unreach.refuted-witness.yml",
          null,
          "SafetyResult Safe",
        ),
        // a no-data-race witness with a multi-follow final segment is confirmed
        Arguments.of(
          "/c/witness-validation/concurrent-data-race.i",
          "/c/witness-validation/concurrent-data-race.witness.yml",
          "--property no-data-race.prp",
          "SafetyResult Unsafe",
        ),
        // a spawned thread's nondet write is pinned via a thread-id-guarded assumption
        Arguments.of(
          "/c/witness-validation/concurrent-nondet.i",
          "/c/witness-validation/concurrent-nondet.witness.yml",
          null,
          "SafetyResult Unsafe",
        ),
        // the same witness pinned to the wrong value is infeasible, hence refuted
        Arguments.of(
          "/c/witness-validation/concurrent-nondet.i",
          "/c/witness-validation/concurrent-nondet.refuted-witness.yml",
          null,
          "SafetyResult Safe",
        ),
        // the spawned thread uses its (kept) argument; the added thread-id param must not break it
        Arguments.of(
          "/c/witness-validation/concurrent-thread-param.i",
          "/c/witness-validation/concurrent-thread-param.witness.yml",
          null,
          "SafetyResult Unsafe",
        ),
        // the same thread-creating call is visited twice, only one visit registers a logical thread
        Arguments.of(
          "/c/witness-validation/concurrent-multi-start.i",
          "/c/witness-validation/concurrent-multi-start.witness.yml",
          null,
          "SafetyResult Unsafe",
        ),
      )
    }

    @JvmStatic
    fun multithreadedRoundTrips(): Stream<Arguments> {
      return Stream.of(
        Arguments.of("/c/witness-validation/concurrent-unreach.i", null),
        Arguments.of("/c/witness-validation/concurrent-data-race.i", "--property no-data-race.prp"),
      )
    }

    /**
     * Tasks declaring a `pthread_mutex_t` whose violation witness must not reference the mutex
     * object in a `c_expression` constraint. The second argument is the C name of the mutex.
     */
    @JvmStatic
    fun mutexWitnessFiles(): Stream<Arguments> {
      return Stream.of(Arguments.of("/c/witness-validation/concurrent-mutex.i", "themutex"))
    }

    /**
     * Tasks whose violation depends on a `__VERIFIER_nondet_*` call: the exported witness must pin
     * the returned value with a `function_return` waypoint located at the call site. The third
     * argument is the source line of the nondet call.
     */
    @JvmStatic
    fun nondetFunctionReturnFiles(): Stream<Arguments> {
      return Stream.of(
        // single-threaded: `int i = __VERIFIER_nondet_int();` on line 5, error needs i == -1
        Arguments.of("/c/litmustest/singlethread/witness_test.c", "--domain PRED_CART", 5),
        // nondet feeding a branch: `if(__VERIFIER_nondet_char() % 2)` on line 5
        Arguments.of("/c/litmustest/singlethread/22nondet.c", "--domain PRED_CART", 5),
        // multi-threaded: the spawned writer does `x = __VERIFIER_nondet_int();` on line 17
        Arguments.of("/c/witness-validation/concurrent-nondet.i", "--domain EXPL", 17),
      )
    }
  }

  /**
   * Regression for the bug where a violation witness referenced a `pthread_mutex_t` object (which
   * Theta models internally as an integer) inside a `c_expression` assumption, e.g. `m == 0`. Such
   * a term is not a valid C expression over the original program, so no emitted `c_expression`
   * constraint may mention a synchronization-object variable.
   */
  @ParameterizedTest
  @MethodSource("mutexWitnessFiles")
  fun testWitnessOmitsSynchronizationObjects(filePath: String, mutexCName: String) {
    val temp = createTempDirectory()
    val params =
      arrayOf(
        "--input-type",
        "C",
        "--input",
        javaClass.getResource(filePath)!!.path,
        "--stacktrace",
        "--debug",
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
    val output = runCatchingOutput(params)
    assertTrue(output.getVerdict().contains("Unsafe")) {
      "Expected an Unsafe verdict (so that a violation witness is emitted) for $filePath, got: ${output.getVerdict()}"
    }

    val witness = temp.getWitness()
    assertTrue(witness.extension == "yml") { "Expected a YAML witness, got $witness" }

    val cExpressionConstraints =
      WitnessYamlConfig.decodeFromString<List<YamlWitness>>(witness.readText())
        .flatMap { it.content }
        .mapNotNull { it.segment }
        .flatten()
        .map { it.waypoint }
        .mapNotNull { it.constraint }
        .filter { it.format == Format.C_EXPRESSION }
        .map { it.value }

    val mutexReference = Regex("\\b${Regex.escape(mutexCName)}\\b")
    assertTrue(cExpressionConstraints.none { mutexReference.containsMatchIn(it) }) {
      "No c_expression constraint may reference the pthread_mutex_t object '$mutexCName', " +
        "but found: ${cExpressionConstraints.filter { mutexReference.containsMatchIn(it) }}"
    }
    println(
      "Witness of $filePath does not reference the mutex '$mutexCName'; c_expression constraints: $cExpressionConstraints"
    )
  }

  @ParameterizedTest
  @MethodSource("nondetFunctionReturnFiles")
  fun testNondetFunctionReturnWaypoint(filePath: String, extraArgs: String?, nondetCallLine: Int) {
    val temp = createTempDirectory()
    val params =
      arrayOf(
        "--input-type",
        "C",
        "--input",
        javaClass.getResource(filePath)!!.path,
        "--stacktrace",
        *(extraArgs?.split(" ")?.toTypedArray() ?: emptyArray()),
        "--debug",
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
    val output = runCatchingOutput(params)
    assertTrue(output.getVerdict().contains("Unsafe")) {
      "Expected an Unsafe verdict (so that a violation witness is emitted) for $filePath, got: ${output.getVerdict()}"
    }

    val witness = temp.getWitness()
    assertTrue(witness.extension == "yml") { "Expected a YAML witness, got $witness" }

    val waypoints =
      WitnessYamlConfig.decodeFromString<List<YamlWitness>>(witness.readText())
        .flatMap { it.content }
        .mapNotNull { it.segment }
        .flatten()
        .map { it.waypoint }
    val functionReturns = waypoints.filter { it.type == WaypointType.FUNCTION_RETURN }

    assertTrue(functionReturns.isNotEmpty()) {
      "Expected a function_return waypoint for the __VERIFIER_nondet_* call in $filePath, " +
        "got waypoint types ${waypoints.map { it.type }}"
    }
    assertTrue(functionReturns.any { it.location.line == nondetCallLine }) {
      "Expected a function_return waypoint at line $nondetCallLine (the nondet call site), " +
        "got lines ${functionReturns.map { it.location.line }}"
    }
    assertTrue(functionReturns.all { it.constraint?.value?.startsWith("\\result") == true }) {
      "Expected every function_return waypoint to constrain the call result as '\\result ...', " +
        "got constraints ${functionReturns.map { it.constraint?.value }}"
    }
    println(
      "Witness of $filePath pins the nondet result(s): ${functionReturns.map { it.constraint?.value }}"
    )
  }

  @ParameterizedTest
  @MethodSource("cFiles")
  fun testCVerifyDirect(filePath: String, extraArgs: String?) {
    val temp = createTempDirectory()
    val params =
      arrayOf(
        "--input-type",
        "C",
        "--input",
        javaClass.getResource(filePath)!!.path,
        "--stacktrace",
        *(extraArgs?.split(" ")?.toTypedArray() ?: emptyArray()),
        "--debug",
        "--output-directory",
        temp.absolutePathString(),
        "--svcomp",
        "--backend",
        "CEGAR",
      )
    val output = runCatchingOutput(params)
    val witness = temp.getWitness()
    if (witness.extension == "yml") {
      val validationOutput = runCatchingOutput(params + "--witness" + witness.absolutePath)

      assertTrue(output.getVerdict() == validationOutput.getVerdict()) {
        "${output.getVerdict()} != ${validationOutput.getVerdict()}"
      }
      println("Verification and validation both agree: task $filePath is ${output.getVerdict()}")
    }
  }

  @ParameterizedTest
  @MethodSource("cFilesShort")
  fun testCVerifyServer(filePath: String, extraArgs: String?) {
    val temp = createTempDirectory()
    val params =
      arrayOf(
        "--input-type",
        "C",
        "--input",
        javaClass.getResource(filePath)!!.path,
        "--stacktrace",
        *(extraArgs?.split(" ")?.toTypedArray() ?: emptyArray()),
        "--debug",
        "--output-directory",
        temp.absolutePathString(),
        "--svcomp",
        "--backend",
        "CEGAR",
      )
    val output = runCatchingOutput(params)
    val witness = temp.getWitness()
    val validationOutput = runCatchingOutput(params + "--witness" + witness.absolutePath)

    assertTrue(output.getVerdict() == validationOutput.getVerdict()) {
      "${output.getVerdict()} != ${validationOutput.getVerdict()}"
    }
    println("Verification and validation both agree: task $filePath is ${output.getVerdict()}")
  }

  @ParameterizedTest
  @MethodSource("multithreadedWitnesses")
  fun testMultithreadedWitnessValidation(
    filePath: String,
    witnessPath: String,
    extraArgs: String?,
    expectedVerdict: String,
  ) {
    val temp = createTempDirectory()
    val params =
      arrayOf(
        "--input-type",
        "C",
        "--input",
        javaClass.getResource(filePath)!!.path,
        "--witness",
        javaClass.getResource(witnessPath)!!.path,
        "--stacktrace",
        *(extraArgs?.split(" ")?.toTypedArray() ?: emptyArray()),
        "--debug",
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
    val output = runCatchingOutput(params)
    assertTrue(output.getVerdict().contains(expectedVerdict)) {
      "Expected $expectedVerdict for $filePath with $witnessPath, got: ${output.getVerdict()}"
    }
    println("Witness validation of $filePath with $witnessPath: ${output.getVerdict()}")
  }

  @ParameterizedTest
  @MethodSource("multithreadedRoundTrips")
  fun testMultithreadedWitnessRoundTrip(filePath: String, extraArgs: String?) {
    val temp = createTempDirectory()
    val params =
      arrayOf(
        "--input-type",
        "C",
        "--input",
        javaClass.getResource(filePath)!!.path,
        "--stacktrace",
        *(extraArgs?.split(" ")?.toTypedArray() ?: emptyArray()),
        "--debug",
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
    val output = runCatchingOutput(params)
    val witness = temp.getWitness()
    assertTrue(witness.extension == "yml") {
      "Expected a YAML (format 2.2) witness for the multi-threaded violation, got $witness"
    }
    val validationOutput = runCatchingOutput(params + "--witness" + witness.absolutePath)

    assertTrue(output.getVerdict() == validationOutput.getVerdict()) {
      "${output.getVerdict()} != ${validationOutput.getVerdict()}"
    }
    println("Round-trip witness validation of $filePath: ${output.getVerdict()}")
  }

  @ParameterizedTest
  @MethodSource("chcFiles")
  fun testCHCVerify(
    filePath: String,
    chcTransformation: ChcFrontend.ChcTransformation,
    extraArgs: String?,
  ) {
    val temp = createTempDirectory()
    val params =
      arrayOf(
        "--input-type",
        "CHC",
        "--chc-transformation",
        chcTransformation.toString(),
        "--input",
        javaClass.getResource(filePath)!!.path,
        "--stacktrace",
        *(extraArgs?.split(" ")?.toTypedArray() ?: emptyArray()),
        "--debug",
        "--output-directory",
        temp.absolutePathString(),
        "--svcomp",
        "--backend",
        "CEGAR",
      )
    val output = runCatchingOutput(params)
    val witness = temp.getWitness()
    val validationOutput = runCatchingOutput(params + "--witness" + witness.absolutePath)

    assertTrue(output.getVerdict() == validationOutput.getVerdict()) {
      "${output.getVerdict()} != ${validationOutput.getVerdict()}"
    }
    println("Verification and validation both agree: task $filePath is ${output.getVerdict()}")
  }

  @ParameterizedTest
  @MethodSource("singleThreadedCFiles")
  fun testCVerifyKind(filePath: String, extraArgs: String?) {
    val temp = createTempDirectory()
    val params =
      arrayOf(
        "--backend",
        "BOUNDED",
        "--input-type",
        "C",
        "--input",
        javaClass.getResource(filePath)!!.path,
        "--stacktrace",
        "--debug",
        "--output-directory",
        temp.absolutePathString(),
        "--svcomp",
      )
    val output = runCatchingOutput(params)
    val witness = temp.getWitness()
    val validationOutput = runCatchingOutput(params + "--witness" + witness.absolutePath)

    assertTrue(output.getVerdict() == validationOutput.getVerdict()) {
      "${output.getVerdict()} != ${validationOutput.getVerdict()}"
    }
    println("Verification and validation both agree: task $filePath is ${output.getVerdict()}")
  }

  @ParameterizedTest
  @MethodSource("finiteStateSpaceC")
  fun testCVerifyMDD(filePath: String, extraArgs: String?) {
    val temp = createTempDirectory()
    val params =
      arrayOf(
        "--backend",
        "MDD",
        "--input-type",
        "C",
        "--input",
        javaClass.getResource(filePath)!!.path,
        "--stacktrace",
        "--debug",
        "--output-directory",
        temp.absolutePathString(),
        "--svcomp",
      )
    val output = runCatchingOutput(params)
    val witness = temp.getWitness()
    val validationOutput = runCatchingOutput(params + "--witness" + witness.absolutePath)

    assertTrue(output.getVerdict() == validationOutput.getVerdict()) {
      "${output.getVerdict()} != ${validationOutput.getVerdict()}"
    }
    println("Verification and validation both agree: task $filePath is ${output.getVerdict()}")
  }

  @ParameterizedTest
  @MethodSource("singleThreadedCFiles")
  fun testCVerifyIMC(filePath: String, extraArgs: String?) {
    val temp = createTempDirectory()
    val params =
      arrayOf(
        "--backend",
        "BOUNDED",
        "--input-type",
        "C",
        "--input",
        javaClass.getResource(filePath)!!.path,
        "--stacktrace",
        "--debug",
        "--output-directory",
        temp.absolutePathString(),
        "--svcomp",
      )
    val output = runCatchingOutput(params)
    val witness = temp.getWitness()
    val validationOutput = runCatchingOutput(params + "--witness" + witness.absolutePath)

    assertTrue(output.getVerdict() == validationOutput.getVerdict()) {
      "${output.getVerdict()} != ${validationOutput.getVerdict()}"
    }
    println("Verification and validation both agree: task $filePath is ${output.getVerdict()}")
  }

  @ParameterizedTest
  @MethodSource("singleThreadedCFiles")
  fun testCVerifyIMCThenKind(filePath: String, extraArgs: String?) {
    val temp = createTempDirectory()
    val params =
      arrayOf(
        "--backend",
        "BOUNDED",
        "--input-type",
        "C",
        "--input",
        javaClass.getResource(filePath)!!.path,
        "--stacktrace",
        "--debug",
        "--output-directory",
        temp.absolutePathString(),
        "--svcomp",
      )
    val output = runCatchingOutput(params)
    val witness = temp.getWitness()
    val validationOutput = runCatchingOutput(params + "--witness" + witness.absolutePath)

    assertTrue(output.getVerdict() == validationOutput.getVerdict()) {
      "${output.getVerdict()} != ${validationOutput.getVerdict()}"
    }
    println("Verification and validation both agree: task $filePath is ${output.getVerdict()}")
  }

  @ParameterizedTest
  @MethodSource("singleThreadedCFiles")
  @Disabled
  fun testCVerifyEmergentPortfolio(filePath: String, extraArgs: String?) {
    Assumptions.assumeTrue(OsHelper.getOs().equals(OsHelper.OperatingSystem.LINUX))
    val temp = createTempDirectory()
    val params =
      arrayOf(
        "--backend",
        "PORTFOLIO",
        "--portfolio",
        "EMERGENT",
        "--input-type",
        "C",
        "--input",
        javaClass.getResource(filePath)!!.path,
        "--stacktrace",
        "--debug",
        "--output-directory",
        temp.absolutePathString(),
        "--svcomp",
      )
    val output = runCatchingOutput(params)
    val witness = temp.getWitness()
    val validationOutput = runCatchingOutput(params + "--witness" + witness.absolutePath)

    assertTrue(output.getVerdict() == validationOutput.getVerdict()) {
      "${output.getVerdict()} != ${validationOutput.getVerdict()}"
    }
    println("Verification and validation both agree: task $filePath is ${output.getVerdict()}")
  }

  @Disabled
  @ParameterizedTest
  @MethodSource("cFilesShortInt")
  fun testCVerifyCHC(filePath: String, extraArgs: String?) {
    Assumptions.assumeTrue(OsHelper.getOs().equals(OsHelper.OperatingSystem.LINUX))
    val temp = createTempDirectory()

    val params =
      arrayOf(
        "--backend",
        "CHC",
        "--input-type",
        "C",
        "--input",
        javaClass.getResource(filePath)!!.path,
        "--stacktrace",
        "--debug",
        "--output-directory",
        temp.absolutePathString(),
        "--svcomp",
      )
    val output = runCatchingOutput(params)
    val witness = temp.getWitness()
    val validationOutput = runCatchingOutput(params + "--witness" + witness.absolutePath)

    assertTrue(output.getVerdict() == validationOutput.getVerdict()) {
      "${output.getVerdict()} != ${validationOutput.getVerdict()}"
    }
    println("Verification and validation both agree: task $filePath is ${output.getVerdict()}")
  }

  @Disabled
  @ParameterizedTest
  @MethodSource("cFilesShortInt")
  fun testCVerifyCHCPortfolio(filePath: String, extraArgs: String?) {
    Assumptions.assumeTrue(OsHelper.getOs().equals(OsHelper.OperatingSystem.LINUX))
    val temp = createTempDirectory()

    val params =
      arrayOf(
        "--backend",
        "portfolio",
        "--portfolio",
        "HORN",
        "--input-type",
        "C",
        "--input",
        javaClass.getResource(filePath)!!.path,
        "--stacktrace",
        "--debug",
        "--output-directory",
        temp.absolutePathString(),
        "--svcomp",
      )
    val output = runCatchingOutput(params)
    val witness = temp.getWitness()
    val validationOutput = runCatchingOutput(params + "--witness" + witness.absolutePath)

    assertTrue(output.getVerdict() == validationOutput.getVerdict()) {
      "${output.getVerdict()} != ${validationOutput.getVerdict()}"
    }
    println("Verification and validation both agree: task $filePath is ${output.getVerdict()}")
  }

  private fun runCatchingOutput(params: Array<String>): String {
    val temp = createTempDirectory()
    val output1 = temp.resolve("stdout_stderr_combined").toFile()
    PrintStream(BufferedOutputStream(FileOutputStream(output1)), true).use { ps ->
      val savedSysOut = System.out
      val savedSysErr = System.err
      System.setOut(ps)
      System.setErr(ps)
      try {
        main(params)
      } catch (e: IllegalStateException) {
        if (!e.message.equals("Done debugging")) {
          throw e
        }
      } finally {
        System.setOut(savedSysOut)
        System.setErr(savedSysErr)
        val out = output1.readText()
        println("============== printing captured output ================")
        print(out)
        println("============ end printing captured output ==============")
      }
      return output1.readText()
    }
  }

  private fun Path.getWitness(): File {
    assertTrue(toFile().exists()) { "$this does not exists" }
    assertTrue(toFile().canRead()) { "$this is not readable" }
    val witnesses = toFile().listFiles().filter { it.name.startsWith("witness") }.toList()
    assertTrue(witnesses.isNotEmpty() && witnesses.size == 1) {
      "$this does not contain exactly one witness ($witnesses)"
    }
    val witness = witnesses[0]
    return witness
  }

  // Round-trip checks compare verdicts only (Safe vs Unsafe). The trace length is an artifact of
  // the particular search and legitimately differs between the verification run and the
  // witness-guided validation run (e.g. a different interleaving is explored under POR), so it is
  // stripped here -- comparing it would over-constrain the test.
  private fun String.getVerdict(): String {
    return (split(System.lineSeparator()).lastOrNull { "SafetyResult" in it } ?: "unsolved")
      .replace(Regex(" Trace length: \\d+"), "")
  }
}
