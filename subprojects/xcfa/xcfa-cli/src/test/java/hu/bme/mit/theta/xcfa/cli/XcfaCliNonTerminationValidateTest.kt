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
import kotlin.io.path.readText
import org.junit.jupiter.api.Assertions.*
import org.junit.jupiter.api.Assumptions
import org.junit.jupiter.api.BeforeAll
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.MethodSource

class XcfaCliNonTerminationValidateTest {
  companion object {

    private val SMTLIB_HOME: Path = SmtLibSolverManager.HOME
    private val solvers = listOf("z3:4.13.0", "mathsat:5.6.10", "eldarica:2.1")

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
    fun witnessFiles(): Stream<Arguments> {
      return Stream.of(
        Arguments.of(
          "/c/nontermination/Pendulum.c",
          "/c/nontermination/Pendulum.yml",
          "--property /c/nontermination/prop/termination.prp",
        ),
        Arguments.of(
          "/c/nontermination/Pendulum-2.c",
          "/c/nontermination/Pendulum-2.yml",
          "--property /c/nontermination/prop/termination.prp",
        ),
        Arguments.of(
          "/c/nontermination/Ex02.c",
          "/c/nontermination/Ex02.yml",
          "--property /c/nontermination/prop/termination.prp",
        ),
        Arguments.of(
          "/c/nontermination/Swingers.c",
          "/c/nontermination/Swingers.yml",
          "--property /c/nontermination/prop/termination.prp",
        ),
      )
    }

    @JvmStatic
    fun wrongWitnessFiles(): Stream<Arguments> {
      return Stream.of(
        //        Arguments.of(
        //          "/c/nontermination/Pendulum-2.c",
        //          "/c/nontermination/Pendulum-2-wrong-loop-wrong.yml",
        //          "--property /c/nontermination/prop/termination.prp",
        //        ),
        Arguments.of(
          "/c/nontermination/Pendulum.c",
          "/c/nontermination/Pendulum-short-wrong.yml",
          "--property /c/nontermination/prop/termination.prp",
        ),
        Arguments.of(
          "/c/nontermination/Swingers.c",
          "/c/nontermination/Swingers-wrong.yml",
          "--property /c/nontermination/prop/termination.prp",
        ),
      )
    }

    @JvmStatic
    fun witnessFilesAdvanced(): Stream<Arguments> {
      return Stream.of(
        Arguments.of(
          "/c/nontermination/Pendulum.c",
          "/c/nontermination/Pendulum.yml",
          "--property /c/nontermination/prop/termination.prp",
        ),
        Arguments.of(
          "/c/nontermination/Pendulum-2.c",
          "/c/nontermination/Pendulum-2.yml",
          "--property /c/nontermination/prop/termination.prp",
        ),
        Arguments.of(
          "/c/nontermination/Ex02.c",
          "/c/nontermination/Ex02.yml",
          "--property /c/nontermination/prop/termination.prp",
        ),
        Arguments.of(
          "/c/nontermination/Swingers.c",
          "/c/nontermination/Swingers.yml",
          "--property /c/nontermination/prop/termination.prp",
        ),
        //        Arguments.of(
        //          "/c/nontermination/NO_03.c",
        //          "/c/nontermination/NO_03.yml",
        //          "--property /c/nontermination/prop/termination.prp",
        //        ),
      )
    }
  }

  @ParameterizedTest
  @MethodSource("witnessFiles")
  fun testCValidateAsgCegar(filePath: String, witnessPath: String, extraArgs: String?) {
    val temp = createTempDirectory()

    val params =
      arrayOf(
        "--input-type",
        "C",
        "--input",
        javaClass.getResource(filePath)!!.path,
        "--witness",
        javaClass.getResource(witnessPath)!!.path,
        "--backend",
        "LIVENESS_CEGAR",
        "--stacktrace",
        *(extraArgs?.split(" ")?.toTypedArray() ?: emptyArray()),
        "--debug",
        "--output-directory",
        temp.absolutePathString(),
        "--svcomp",
      )
    main(params)
    assertTrue(temp.resolve("witness.yml").exists())
    assertTrue(isWitnessViolation(temp), "No violation witness was produced!")
  }

  @ParameterizedTest
  @MethodSource("witnessFiles")
  fun testCValidateServer(filePath: String, witnessPath: String, extraArgs: String?) {
    val temp = createTempDirectory()

    val params =
      arrayOf(
        "--input-type",
        "C",
        "--input",
        javaClass.getResource(filePath)!!.path,
        "--witness",
        javaClass.getResource(witnessPath)!!.path,
        "--backend",
        "LIVENESS_CEGAR",
        "--stacktrace",
        *(extraArgs?.split(" ")?.toTypedArray() ?: emptyArray()),
        "--debug",
        "--output-directory",
        temp.absolutePathString(),
        "--svcomp",
      )
    try {
      main(params)
      assertTrue(temp.resolve("witness.yml").exists())
      assertTrue(isWitnessViolation(temp), "No violation witness was produced!")
    } catch (e: IllegalStateException) {
      if (!e.message.equals("Done debugging")) {
        throw e
      }
    }
  }

  @ParameterizedTest
  @MethodSource("witnessFiles")
  fun testCValidateTerminationPortfolio(filePath: String, witnessPath: String, extraArgs: String?) {
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
        "--witness",
        javaClass.getResource(witnessPath)!!.path,
        "--stacktrace",
        *(extraArgs?.split(" ")?.toTypedArray() ?: emptyArray()),
        "--debug",
        "--output-directory",
        temp.absolutePathString(),
        "--svcomp",
      )
    try {
      main(params)
      assertTrue(temp.resolve("witness.yml").exists())
      val witnessContents = temp.resolve("witness.yml").toFile().readText()
      assertTrue(isWitnessViolation(temp), "No violation witness was produced!")
    } catch (e: Throwable) {
      if (!e.toString().contains("Done debugging")) {
        throw e
      }
    }
  }

  @ParameterizedTest
  @MethodSource("witnessFilesAdvanced")
  fun testCValidateKind(filePath: String, witnessPath: String, extraArgs: String?) {
    val temp = createTempDirectory()

    val params =
      arrayOf(
        "--backend",
        "KIND",
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
      )
    main(params)
    assertTrue(temp.resolve("witness.yml").exists())
    assertTrue(isWitnessViolation(temp), "No violation witness was produced!")
  }

  @ParameterizedTest
  @MethodSource("witnessFilesAdvanced")
  fun testCValidateMDD(filePath: String, witnessPath: String, extraArgs: String?) {
    val temp = createTempDirectory()

    val params =
      arrayOf(
        "--backend",
        "MDD",
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
      )
    main(params)
  }

  @ParameterizedTest
  @MethodSource("witnessFilesAdvanced")
  fun testCValidateIMC(filePath: String, witnessPath: String, extraArgs: String?) {
    val temp = createTempDirectory()

    val params =
      arrayOf(
        "--backend",
        "IMC",
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
      )
    main(params)
    assertTrue(temp.resolve("witness.yml").exists())
    assertTrue(isWitnessViolation(temp), "No violation witness was produced!")
  }

  @ParameterizedTest
  @MethodSource("witnessFilesAdvanced")
  fun testCValidateEmergentPortfolio(filePath: String, witnessPath: String, extraArgs: String?) {
    val temp = createTempDirectory()

    Assumptions.assumeTrue(OsHelper.getOs().equals(OsHelper.OperatingSystem.LINUX))
    val params =
      arrayOf(
        "--backend",
        "PORTFOLIO",
        "--portfolio",
        "EMERGENT",
        "--input-type",
        "C",
        "--loglevel",
        "INFO",
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
      )
    main(params)
    assertTrue(temp.resolve("witness.yml").exists())
    assertTrue(isWitnessViolation(temp), "No violation witness was produced!")
  }

  @ParameterizedTest
  @MethodSource("witnessFilesAdvanced")
  fun testCValidateCHC(filePath: String, witnessPath: String, extraArgs: String?) {
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
        "--witness",
        javaClass.getResource(witnessPath)!!.path,
        "--loglevel",
        "INFO",
        "--stacktrace",
        *(extraArgs?.split(" ")?.toTypedArray() ?: emptyArray()),
        "--debug",
        "--output-directory",
        temp.absolutePathString(),
        "--svcomp",
      )
    main(params)
    assertTrue(isWitnessViolation(temp), "No violation witness was produced!")
  }

  private fun isWitnessViolation(temp: Path): Boolean {
    assertTrue(temp.resolve("witness.yml").exists())
    val witnessContents = temp.resolve("witness.yml").toFile().readText()
    return "entry_type: violation_sequence" in witnessContents
  }

  /////////// wrong witnesses ///////////

  @ParameterizedTest
  @MethodSource("wrongWitnessFiles")
  fun testCValidateWrongAsgCegar(filePath: String, witnessPath: String, extraArgs: String?) {
    if (true) return
    val temp = createTempDirectory()

    val params =
      arrayOf(
        "--input-type",
        "C",
        "--input",
        javaClass.getResource(filePath)!!.path,
        "--witness",
        javaClass.getResource(witnessPath)!!.path,
        "--backend",
        "LIVENESS_CEGAR",
        "--stacktrace",
        *(extraArgs?.split(" ")?.toTypedArray() ?: emptyArray()),
        "--debug",
        "--output-directory",
        temp.absolutePathString(),
        "--svcomp",
      )
    main(params)
    // TODO: add correctness check once correctness termination witnesses are added
    assertFalse(isWitnessViolation(temp), "A violation witness was produced!")
  }

  @ParameterizedTest
  @MethodSource("wrongWitnessFiles")
  fun testCValidateWrongTerminationPortfolio(
    filePath: String,
    witnessPath: String,
    extraArgs: String?,
  ) {
    if (true) return
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
        "--witness",
        javaClass.getResource(witnessPath)!!.path,
        "--stacktrace",
        *(extraArgs?.split(" ")?.toTypedArray() ?: emptyArray()),
        "--debug",
        "--output-directory",
        temp.absolutePathString(),
        "--svcomp",
      )
    try {
      main(params)
      // TODO: add correctness check once correctness termination witnesses are added
      assertFalse(isWitnessViolation(temp), "A violation witness was produced!")
    } catch (e: Throwable) {
      if (!e.toString().contains("Done debugging")) {
        throw e
      }
    }
  }

  @ParameterizedTest
  @MethodSource("wrongWitnessFiles")
  fun testCValidateWrongKind(filePath: String, witnessPath: String, extraArgs: String?) {
    if (true) return
    val temp = createTempDirectory()

    val params =
      arrayOf(
        "--backend",
        "KIND",
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
      )
    main(params)
    // TODO: add correctness check once correctness termination witnesses are added
    assertFalse(isWitnessViolation(temp), "A violation witness was produced!")
  }

  @ParameterizedTest
  @MethodSource("wrongWitnessFiles")
  fun testCValidateWrongBoundedPortfolio(
    filePath: String,
    witnessPath: String,
    extraArgs: String?,
  ) {
    val temp = createTempDirectory()

    Assumptions.assumeTrue(OsHelper.getOs().equals(OsHelper.OperatingSystem.LINUX))
    val params =
      arrayOf(
        "--backend",
        "PORTFOLIO",
        "--portfolio",
        "EMERGENT",
        "--input-type",
        "C",
        "--loglevel",
        "INFO",
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
      )
    main(params)
    // TODO: add correctness check once correctness termination witnesses are added
    assertFalse(isWitnessViolation(temp), "A violation witness was produced!")
  }

  @ParameterizedTest
  @MethodSource("wrongWitnessFiles")
  fun testCValidateWrongCHC(filePath: String, witnessPath: String, extraArgs: String?) {
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
        "--witness",
        javaClass.getResource(witnessPath)!!.path,
        "--loglevel",
        "INFO",
        "--stacktrace",
        *(extraArgs?.split(" ")?.toTypedArray() ?: emptyArray()),
        "--debug",
        "--output-directory",
        temp.absolutePathString(),
        "--svcomp",
      )
    main(params)
    // TODO: add correctness check once correctness termination witnesses are added
    assertFalse(isWitnessViolation(temp), "A violation witness was produced!")
  }

  @ParameterizedTest
  @MethodSource("wrongWitnessFiles")
  fun testCValidateWrongIMC(filePath: String, witnessPath: String, extraArgs: String?) {
    val temp = createTempDirectory()

    val params =
      arrayOf(
        "--backend",
        "BOUNDED",
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
      )
    main(params)
    // TODO: add correctness check once correctness termination witnesses are added
    assertFalse(isWitnessViolation(temp), "A violation witness was produced!")
  }
}
