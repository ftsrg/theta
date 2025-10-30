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

import hu.bme.mit.theta.common.OsHelper
import hu.bme.mit.theta.common.logging.ConsoleLogger
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.solver.smtlib.SmtLibSolverManager
import hu.bme.mit.theta.xcfa.cli.XcfaCli.Companion.main
import java.nio.file.Path
import java.util.stream.Stream
import kotlin.io.path.absolutePathString
import kotlin.io.path.createTempDirectory
import kotlin.io.path.exists
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Assumptions
import org.junit.jupiter.api.BeforeAll
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.MethodSource

class XcfaCliNonTerminationVerifyTest {
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
        Arguments.of(
          "/c/nontermination/NO_03.c",
          "--property /c/nontermination/prop/termination.prp",
        ),
        Arguments.of(
          "/c/nontermination/Pendulum.c",
          "--property /c/nontermination/prop/termination.prp",
        ),
        Arguments.of(
          "/c/nontermination/Pendulum-2.c",
          "--property /c/nontermination/prop/termination.prp",
        ),
        Arguments.of(
          "/c/nontermination/for_infinite_loop_1.c",
          "--property /c/nontermination/prop/termination.prp",
        ),
      )
    }

    @JvmStatic
    fun cFilesAdvanced(): Stream<Arguments> {
      return Stream.of(
        Arguments.of(
          "/c/nontermination/NO_03.c",
          "--property /c/nontermination/prop/termination.prp",
        ),
        Arguments.of(
          "/c/nontermination/Pendulum.c",
          "--property /c/nontermination/prop/termination.prp",
        ),
        Arguments.of(
          "/c/nontermination/Pendulum-2.c",
          "--property /c/nontermination/prop/termination.prp",
        ),
        Arguments.of(
          "/c/nontermination/Ex02.c",
          "--property /c/nontermination/prop/termination.prp",
        ),
        Arguments.of(
          "/c/nontermination/Swingers.c",
          "--property /c/nontermination/prop/termination.prp",
        ),
      )
    }
  }

  @ParameterizedTest
  @MethodSource("cFiles")
  fun testCVerifyAsgCegar(filePath: String, extraArgs: String?) {
    val temp = createTempDirectory()

    val params =
      arrayOf(
        "--input-type",
        "C",
        "--input",
        javaClass.getResource(filePath)!!.path,
        "--backend",
        "LIVENESS_CEGAR",
        "--stacktrace",
        *(extraArgs?.split(" ")?.toTypedArray() ?: emptyArray()),
        "--debug",
        "--output-directory",
        temp.absolutePathString(),
        "--enable-output",
      )
    main(params)
    assertTrue(temp.resolve("witness.yml").exists())
    val witnessContents = temp.resolve("witness.yml").toFile().readText()
    assertTrue(
      "entry_type: \"violation_sequence\"" in witnessContents,
      "No violation witness was produced!",
    )
  }

  @ParameterizedTest
  @MethodSource("cFiles")
  fun testCVerifyServer(filePath: String, extraArgs: String?) {
    val temp = createTempDirectory()

    val params =
      arrayOf(
        "--input-type",
        "C",
        "--input",
        javaClass.getResource(filePath)!!.path,
        "--backend",
        "LIVENESS_CEGAR",
        "--stacktrace",
        *(extraArgs?.split(" ")?.toTypedArray() ?: emptyArray()),
        "--debug",
        "--output-directory",
        temp.absolutePathString(),
        "--enable-output",
      )
    try {
      main(params)
      assertTrue(temp.resolve("witness.yml").exists())
      val witnessContents = temp.resolve("witness.yml").toFile().readText()
      assertTrue(
        "entry_type: \"violation_sequence\"" in witnessContents,
        "No violation witness was produced!",
      )
    } catch (e: IllegalStateException) {
      if (!e.message.equals("Done debugging")) {
        throw e
      }
    }
  }

  @ParameterizedTest
  @MethodSource("cFiles")
  fun testCVerifyTerminationPortfolio(filePath: String, extraArgs: String?) {
    val temp = createTempDirectory()

    val params =
      arrayOf(
        "--input-type",
        "C",
        "--backend",
        "PORTFOLIO",
        "--portfolio",
        "TERMINATION",
        "--input",
        javaClass.getResource(filePath)!!.path,
        "--stacktrace",
        *(extraArgs?.split(" ")?.toTypedArray() ?: emptyArray()),
        "--debug",
        "--output-directory",
        temp.absolutePathString(),
        "--enable-output",
      )
    try {
      main(params)
      assertTrue(temp.resolve("witness.yml").exists())
      val witnessContents = temp.resolve("witness.yml").toFile().readText()
      assertTrue(
        "entry_type: \"violation_sequence\"" in witnessContents,
        "No violation witness was produced!",
      )
    } catch (e: Throwable) {
      if (!e.toString().contains("Done debugging")) {
        throw e
      }
    }
  }

  @ParameterizedTest
  @MethodSource("cFilesAdvanced")
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
        *(extraArgs?.split(" ")?.toTypedArray() ?: emptyArray()),
        "--debug",
        "--output-directory",
        temp.absolutePathString(),
        "--enable-output",
      )
    main(params)
    assertTrue(temp.resolve("witness.yml").exists())
    val witnessContents = temp.resolve("witness.yml").toFile().readText()
    assertTrue(
      "entry_type: \"violation_sequence\"" in witnessContents,
      "No violation witness was produced!",
    )
  }

  @ParameterizedTest
  @MethodSource("cFiles")
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
        *(extraArgs?.split(" ")?.toTypedArray() ?: emptyArray()),
        "--debug",
        "--output-directory",
        temp.absolutePathString(),
        "--enable-output",
      )
    main(params)
  }

  @ParameterizedTest
  @MethodSource("cFilesAdvanced")
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
        *(extraArgs?.split(" ")?.toTypedArray() ?: emptyArray()),
        "--debug",
        "--output-directory",
        temp.absolutePathString(),
        "--enable-output",
      )
    main(params)
    assertTrue(temp.resolve("witness.yml").exists())
    val witnessContents = temp.resolve("witness.yml").toFile().readText()
    assertTrue(
      "entry_type: \"violation_sequence\"" in witnessContents,
      "No violation witness was produced!",
    )
  }

  @ParameterizedTest
  @MethodSource("cFilesAdvanced")
  fun testCVerifyBoundedPortfolio(filePath: String, extraArgs: String?) {
    val temp = createTempDirectory()

    Assumptions.assumeTrue(OsHelper.getOs().equals(OsHelper.OperatingSystem.LINUX))
    val params =
      arrayOf(
        "--backend",
        "PORTFOLIO",
        "--portfolio",
        "BOUNDED",
        "--input-type",
        "C",
        "--loglevel",
        "INFO",
        "--input",
        javaClass.getResource(filePath)!!.path,
        "--stacktrace",
        *(extraArgs?.split(" ")?.toTypedArray() ?: emptyArray()),
        "--debug",
        "--output-directory",
        temp.absolutePathString(),
        "--enable-output",
      )
    main(params)
    assertTrue(temp.resolve("witness.yml").exists())
    val witnessContents = temp.resolve("witness.yml").toFile().readText()
    assertTrue(
      "entry_type: \"violation_sequence\"" in witnessContents,
      "No violation witness was produced!",
    )
  }

  @ParameterizedTest
  @MethodSource("cFilesAdvanced")
  fun testCVerifyCHC(filePath: String, extraArgs: String?) {
    val temp = createTempDirectory()

    Assumptions.assumeTrue(OsHelper.getOs().equals(OsHelper.OperatingSystem.LINUX))

    val params =
      arrayOf(
        "--solver",
        "eldarica:2.1",
        "--backend",
        "CHC",
        "--input-type",
        "C",
        "--input",
        javaClass.getResource(filePath)!!.path,
        "--loglevel",
        "INFO",
        "--stacktrace",
        *(extraArgs?.split(" ")?.toTypedArray() ?: emptyArray()),
        "--debug",
        "--output-directory",
        temp.absolutePathString(),
        "--enable-output",
      )
    main(params)
    assertTrue(temp.resolve("witness.yml").exists())
    val witnessContents = temp.resolve("witness.yml").toFile().readText()
    assertTrue(
      "entry_type: \"violation_sequence\"" in witnessContents,
      "No violation witness was produced!",
    )
  }
}
