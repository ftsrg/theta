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

import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.core.decl.Decls.Param
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Exists
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Not
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Or
import hu.bme.mit.theta.core.type.bvtype.BvExprs.BvType
import hu.bme.mit.theta.core.type.bvtype.BvExprs.Eq as BvEq
import hu.bme.mit.theta.core.type.inttype.IntExprs.*
import hu.bme.mit.theta.core.utils.BvUtils
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.xcfa.cli.checkers.getCegarChecker
import hu.bme.mit.theta.xcfa.cli.params.getDefaultPredCegarConfig
import hu.bme.mit.theta.xcfa.cli.utils.ensureDefaultSolversRegistered
import hu.bme.mit.theta.xcfa.dss.analysis.DssAuxVars
import hu.bme.mit.theta.xcfa.dss.analysis.DssCheckerRoster
import hu.bme.mit.theta.xcfa.dss.decomposition.LinearBlockDecomposition
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.collectVars
import java.io.ByteArrayInputStream
import java.io.ByteArrayOutputStream
import java.io.DataInputStream
import java.io.DataOutputStream
import java.io.File
import java.math.BigInteger
import java.time.Duration
import kotlin.system.exitProcess
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTimeoutPreemptively
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.assertThrows

/**
 * The x/y loop of [CyclicBlockGraphAnalysisTest] (the paper's running example), plus a bitvector
 * variable for the codec test. Every worker process builds it again, as xcfa-cli parses the input.
 */
internal fun processFixtureXcfa(incrementY: Boolean): XCFA =
  xcfa("xy-loop") {
    val main =
      procedure("main") {
        "x" type Int()
        "y" type Int()
        "b" type BvType(8)
        (init to "loophead") {
          "x" assign "0"
          "y" assign "0"
        }
        ("loophead" to "body") { assume("(< x 10)") }
        ("loophead" to "afterloop") { assume("(>= x 10)") }
        if (incrementY) {
          ("body" to "loophead") {
            "x" assign "(+ x 1)"
            "y" assign "(+ y 1)"
          }
        } else {
          ("body" to "loophead") { "x" assign "(+ x 1)" }
        }
        ("afterloop" to final) { assume("(= x y)") }
        ("afterloop" to err) { assume("(/= x y)") }
      }
    main.start()
  }

private fun cegarChecker(xcfa: XCFA) =
  getCegarChecker(
    xcfa,
    emptySet(),
    ParseContext(),
    getDefaultPredCegarConfig(),
    NullLogger.getInstance(),
  )

/**
 * The worker side of the tests: `<safe|unsafe> <port> <index> <blocks>`, or `crash` instead of the
 * fixture for a worker that dies during its first request.
 */
object DssProcessTestWorker {

  @JvmStatic
  fun main(args: Array<String>) {
    val crash = args[0] == "crash"
    ensureDefaultSolversRegistered(getDefaultPredCegarConfig(), NullLogger.getInstance())
    val xcfa = processFixtureXcfa(incrementY = args[0] == "safe")
    val procedure = xcfa.procedures.single()
    val blockGraph = LinearBlockDecomposition().decompose(procedure)
    val roster = DssCheckerRoster(listOf { x -> cegarChecker(x) })
    val blocks = blockGraph.blocks.associateBy { it.id }
    val behaviors =
      args[3].split(",").associateWith { id ->
        if (crash)
          object : DssBlockBehavior {
            override fun initialMessages(): Collection<DssMessage> = exitProcess(3)

            override fun onPostCondition(message: DssPostConditionMessage) = exitProcess(3)

            override fun onViolationCondition(message: DssViolationConditionMessage) =
              exitProcess(3)
          }
        else PredicateBlockBehavior(xcfa, procedure, blocks.getValue(id), roster)
      }
    serveDssBlocks(
      args[1].toInt(),
      args[2].toInt(),
      blockGraph.fingerprint(),
      behaviors,
      DssExprCodec(xcfa),
    )
    exitProcess(0)
  }
}

class DssProcessExecutorTest {

  private fun launcher(fixture: String) = DssWorkerLauncher { index, blockIds, port ->
    val java = File(System.getProperty("java.home"), "bin/java").path
    ProcessBuilder(
        java,
        "-Xss120m",
        "-Djava.library.path=${System.getProperty("java.library.path")}",
        "-cp",
        System.getProperty("java.class.path"),
        DssProcessTestWorker::class.java.name,
        fixture,
        "$port",
        "$index",
        blockIds.joinToString(","),
      )
      .redirectErrorStream(true)
      .redirectOutput(ProcessBuilder.Redirect.DISCARD)
      .start()
  }

  private fun runInProcesses(incrementY: Boolean, fixture: String, maxProcesses: Int = 0) =
    assertTimeoutPreemptively<DssResult>(Duration.ofSeconds(180)) {
      val xcfa = processFixtureXcfa(incrementY)
      val blockGraph = LinearBlockDecomposition().decompose(xcfa.procedures.single())
      runDssActorsInProcesses(blockGraph, launcher(fixture), DssExprCodec(xcfa), maxProcesses)
    }

  @Test
  fun `expressions over program and auxiliary variables survive the codec`() {
    val xcfa = processFixtureXcfa(incrementY = true)
    val vars = xcfa.collectVars().associateBy { it.name }
    val x = vars.getValue("x").ref as Expr<hu.bme.mit.theta.core.type.inttype.IntType>
    val y = vars.getValue("y").ref as Expr<hu.bme.mit.theta.core.type.inttype.IntType>
    val b = vars.getValue("b").ref as Expr<hu.bme.mit.theta.core.type.bvtype.BvType>
    val aux0 = DssAuxVars.of(0, Int()).ref as Expr<hu.bme.mit.theta.core.type.inttype.IntType>
    val aux1 = DssAuxVars.of(1, BvType(8)).ref as Expr<hu.bme.mit.theta.core.type.bvtype.BvType>
    val p = Param("p", Int())
    val exprs: List<Expr<BoolType>> =
      listOf(
        True(),
        And(Lt(x, Int(10)), Not(Eq(x, y))),
        Or(Eq(Add(x, aux0), Int(-3)), BvEq(b, aux1)),
        Exists(listOf(p), Eq(Add(p.ref, aux0), y)),
        BvEq(b, BvUtils.bigIntegerToNeutralBvLitExpr(BigInteger.valueOf(200), 8)),
      )
    val codec = DssExprCodec(xcfa)
    val bytes = ByteArrayOutputStream()
    DataOutputStream(bytes).use { out -> exprs.forEach { codec.write(out, it) } }
    val input = DataInputStream(ByteArrayInputStream(bytes.toByteArray()))
    exprs.forEach { expr ->
      val read = codec.read(input)
      // A bound variable is declared anew, and declarations are equal by identity only
      if (expr === exprs[3]) assertEquals(expr.toString(), read.toString())
      else assertEquals(expr, read)
    }
  }

  @Test
  fun `process executor reproduces the SAFE verdict with legacy Z3`() {
    assertEquals(DssResult.SAFE, runInProcesses(incrementY = true, fixture = "safe"))
  }

  @Test
  fun `process executor reproduces the UNSAFE verdict with legacy Z3`() {
    assertEquals(DssResult.UNSAFE, runInProcesses(incrementY = false, fixture = "unsafe"))
  }

  @Test
  fun `process executor with fewer processes than blocks reproduces the SAFE verdict`() {
    assertEquals(
      DssResult.SAFE,
      runInProcesses(incrementY = true, fixture = "safe", maxProcesses = 2),
    )
  }

  @Test
  fun `a worker process that dies fails the run instead of hanging it`() {
    val e = assertThrows<Throwable> { runInProcesses(incrementY = true, fixture = "crash") }
    assertTrue(
      generateSequence(e) { it.cause }.any { it is DssWorkerException },
      "expected a DssWorkerException, got $e",
    )
  }
}
