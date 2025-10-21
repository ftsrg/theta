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
import hu.bme.mit.theta.frontend.chc.ChcFrontend
import hu.bme.mit.theta.solver.smtlib.SmtLibSolverManager
import hu.bme.mit.theta.xcfa.cli.XcfaCli.Companion.main
import java.nio.file.Path
import java.util.concurrent.TimeUnit
import java.util.stream.Stream
import kotlin.io.path.absolutePathString
import kotlin.io.path.createTempDirectory
import kotlin.io.path.exists
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Assumptions
import org.junit.jupiter.api.BeforeAll
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.Timeout
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.MethodSource

class XcfaCliValidateTest {
  companion object {

    private val SMTLIB_HOME: Path = SmtLibSolverManager.HOME
    private val solvers = listOf("z3:4.13.0", "mathsat:5.6.10")

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
        Arguments.of("/c/dekker.i", "--search DFS --por-level SPOR"),
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
        Arguments.of("/c/litmustest/singlethread/17recursive.c", null),
        Arguments.of("/c/litmustest/singlethread/18multithread.c", "--search DFS --por-level SPOR"),
        Arguments.of("/c/litmustest/singlethread/19dportest.c", "--search DFS --por-level SPOR"),
        Arguments.of("/c/litmustest/singlethread/20testinline.c", null),
        Arguments.of("/c/litmustest/singlethread/21namecollision.c", null),
        Arguments.of("/c/litmustest/singlethread/22nondet.c", null),
        Arguments.of("/c/litmustest/singlethread/23overflow.c", "--domain PRED_CART"),
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
        Arguments.of("/c/dekker.i", "--search DFS --por-level SPOR"),
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
  }

  @ParameterizedTest
  @MethodSource("cFiles")
  fun testCVerifyDirect(filePath: String, extraArgs: String?) {
    val params =
      arrayOf(
        "--input-type",
        "C",
        "--input",
        javaClass.getResource(filePath)!!.path,
        "--stacktrace",
        *(extraArgs?.split(" ")?.toTypedArray() ?: emptyArray()),
        "--debug",
      )
    main(params)
  }

  @ParameterizedTest
  @MethodSource("cFilesShort")
  fun testCVerifyServer(filePath: String, extraArgs: String?) {
    val params =
      arrayOf(
        "--input-type",
        "C",
        "--input",
        javaClass.getResource(filePath)!!.path,
        "--stacktrace",
        *(extraArgs?.split(" ")?.toTypedArray() ?: emptyArray()),
        "--debug",
      )
    try {
      main(params)
    } catch (e: IllegalStateException) {
      if (!e.message.equals("Done debugging")) {
        throw e
      }
    }
  }

  @ParameterizedTest
  @MethodSource("cFilesShort")
  fun testCVerifyPortfolio(filePath: String, extraArgs: String?) {
    val params =
      arrayOf(
        "--input-type",
        "C",
        "--backend",
        "PORTFOLIO",
        "--portfolio",
        javaClass.getResource("/simple.kts")!!.path,
        "--input",
        javaClass.getResource(filePath)!!.path,
        "--stacktrace",
        "--debug",
      )
    try {
      main(params)
    } catch (e: Throwable) {
      if (!e.toString().contains("Done debugging")) {
        throw e
      }
    }
  }

  @Test
  fun testCVerifyBuiltInPortfolio() {
    val params =
      arrayOf(
        "--input-type",
        "C",
        "--backend",
        "PORTFOLIO",
        "--portfolio",
        "COMPLEX",
        "--input",
        javaClass.getResource("/c/dekker.i")!!.path,
        "--stacktrace",
        "--debug",
      )
    try {
      main(params)
    } catch (e: Throwable) {
      if (!e.toString().contains("Done debugging")) {
        throw e
      }
    }
  }

  //  @ParameterizedTest
  //  @MethodSource("cFiles")
  fun testCWitness(filePath: String, extraArgs: String?) {
    val temp = createTempDirectory()
    val params =
      arrayOf(
        "--enable-output",
        "--input-type",
        "C",
        "--input",
        javaClass.getResource(filePath)!!.path,
        "--stacktrace",
        *(extraArgs?.split(" ")?.toTypedArray() ?: emptyArray()),
        "--output-directory",
        temp.absolutePathString(),
        "--debug",
      )
    main(params)
    Assertions.assertTrue(temp.resolve("xcfa.json").exists())
    Assertions.assertTrue(
      temp.resolve("arg-true.dot").exists() || temp.resolve("arg-false.dot").exists()
    )
    temp.toFile().deleteRecursively()
  }

  @ParameterizedTest
  @MethodSource("chcFiles")
  fun testCHCVerify(
    filePath: String,
    chcTransformation: ChcFrontend.ChcTransformation,
    extraArgs: String?,
  ) {
    main(
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
      )
    )
  }

  @ParameterizedTest
  @MethodSource("singleThreadedCFiles")
  fun testCVerifyKind(filePath: String, extraArgs: String?) {
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
      )
    main(params)
  }

  @ParameterizedTest
  @MethodSource("finiteStateSpaceC")
  @Timeout(value = 10, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun testCVerifyMDD(filePath: String, extraArgs: String?) {
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
      )
    main(params)
  }

  @ParameterizedTest
  @MethodSource("singleThreadedCFiles")
  fun testCVerifyIMC(filePath: String, extraArgs: String?) {
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
      )
    main(params)
  }

  @ParameterizedTest
  @MethodSource("singleThreadedCFiles")
  fun testCVerifyIMCThenKind(filePath: String, extraArgs: String?) {
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
      )
    main(params)
  }

  @ParameterizedTest
  @MethodSource("singleThreadedCFiles")
  fun testCVerifyBoundedPortfolio(filePath: String, extraArgs: String?) {
    Assumptions.assumeTrue(OsHelper.getOs().equals(OsHelper.OperatingSystem.LINUX))
    val params =
      arrayOf(
        "--backend",
        "PORTFOLIO",
        "--portfolio",
        "BOUNDED",
        "--input-type",
        "C",
        "--input",
        javaClass.getResource(filePath)!!.path,
        "--stacktrace",
        "--debug",
      )
    main(params)
  }

  @ParameterizedTest
  @MethodSource("cFilesShortInt")
  fun testCVerifyCHC(filePath: String, extraArgs: String?) {
    Assumptions.assumeTrue(OsHelper.getOs().equals(OsHelper.OperatingSystem.LINUX))

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
      )
    main(params)
  }

  @ParameterizedTest
  @MethodSource("cFilesShortInt")
  fun testCVerifyCHCPortfolio(filePath: String, extraArgs: String?) {
    Assumptions.assumeTrue(OsHelper.getOs().equals(OsHelper.OperatingSystem.LINUX))

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
      )
    main(params)
  }
}
