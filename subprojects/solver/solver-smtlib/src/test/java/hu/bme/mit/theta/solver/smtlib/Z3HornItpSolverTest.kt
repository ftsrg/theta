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
package hu.bme.mit.theta.solver.smtlib

import com.google.common.collect.ImmutableList
import hu.bme.mit.theta.common.OsHelper
import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.functype.FuncExprs
import hu.bme.mit.theta.core.type.functype.FuncType
import hu.bme.mit.theta.core.type.inttype.IntExprs.*
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.solver.HornItpSolver
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.solver.SolverStatus
import hu.bme.mit.theta.solver.smtlib.solver.installer.SmtLibSolverInstallerException
import java.io.IOException
import java.util.concurrent.TimeUnit
import org.junit.jupiter.api.*

class SmtLibHornItpSolverTest {

  companion object {
    private val installedSolvers: MutableList<Pair<String, String>> = mutableListOf()
    private var solverManager: SmtLibSolverManager? = null
    private val solverFactories: MutableMap<String, SolverFactory> = mutableMapOf()

    private val solversToInstall =
      listOf(Pair("z3", "4.13.0"), Pair("eldarica", "2.1"), Pair("golem", "0.6.5"))

    @BeforeAll
    @JvmStatic
    @Throws(SmtLibSolverInstallerException::class, IOException::class)
    fun init() {
      if (OsHelper.getOs() == OsHelper.OperatingSystem.LINUX) {
        val home = SmtLibSolverManager.HOME
        solverManager = SmtLibSolverManager.create(home, NullLogger.getInstance())

        for ((name, version) in solversToInstall) {
          try {
            solverManager!!.install(name, version, version, null, false)
            installedSolvers.add(name to version)
          } catch (e: SmtLibSolverInstallerException) {
            // e.printStackTrace()
          }

          val factory = solverManager!!.getSolverFactory(name, version)
          solverFactories[name] = factory
        }
      }
    }

    @AfterAll
    @JvmStatic
    @Throws(SmtLibSolverInstallerException::class)
    fun destroy() {
      installedSolvers.forEach { (name, version) -> solverManager?.uninstall(name, version) }
      installedSolvers.clear()
      solverFactories.clear()
    }
  }

  private val solvers: MutableMap<String, HornItpSolver> = mutableMapOf()

  var a: Expr<IntType>? = null
  var b: Expr<IntType>? = null
  var c: Expr<IntType>? = null
  var d: Expr<IntType>? = null
  var e: Expr<IntType>? = null
  var f: Expr<FuncType<IntType, IntType>>? = null
  var g: Expr<FuncType<IntType, IntType>>? = null

  @BeforeEach
  fun initialize() {
    solvers["Z3"] = HornItpSolver(solverFactories["z3"]!!.createSolver(), solverFactories["z3"])
    solvers["Eldarica"] =
      HornItpSolver(solverFactories["z3"]!!.createSolver(), solverFactories["eldarica"])
    solvers["Golem"] =
      HornItpSolver(solverFactories["z3"]!!.createSolver(), solverFactories["golem"])

    val ad = Decls.Const("a", Int())
    val bd = Decls.Const("b", Int())
    val cd = Decls.Const("c", Int())
    val dd = Decls.Const("d", Int())
    val ed = Decls.Const("e", Int())
    val fd = Decls.Const("f", FuncExprs.Func(Int(), Int()))
    val gd = Decls.Const("g", FuncExprs.Func(Int(), Int()))

    a = ad.ref
    b = bd.ref
    c = cd.ref
    d = dd.ref
    e = ed.ref
    f = fd.ref
    g = gd.ref
  }

  @Test
  fun testBinaryInterpolation() {
    for ((name, solver) in solvers) {
      val A = solver.createMarker()
      val B = solver.createMarker()
      val pattern = solver.createBinPattern(A, B)

      solver.add(A, Eq(a, b))
      solver.add(A, Eq(a, c))
      solver.add(B, Eq(b, d))
      solver.add(B, Neq(c, d))

      solver.check()
      Assertions.assertEquals(SolverStatus.UNSAT, solver.status)
      val sw = com.google.common.base.Stopwatch.createStarted()
      val itp = solver.getInterpolant(pattern)
      sw.stop()

      println("$name: ${itp.eval(A)} (${sw.elapsed(TimeUnit.MILLISECONDS)} ms)")
      Assertions.assertTrue(ExprUtils.getVars(itp.eval(A)).size <= 3)
    }
  }

  @Test
  fun testLIA() {
    for ((name, solver) in solvers.filter { it.key != "golem" }) {
      val A = solver.createMarker()
      val B = solver.createMarker()
      val pattern = solver.createBinPattern(A, B)

      solver.add(A, Eq(b, Mul(ImmutableList.of(Int(2), a!!))))
      solver.add(B, Eq(b, Add(ImmutableList.of(Mul(ImmutableList.of(Int(2), c!!)), Int(1)))))

      solver.check()
      Assertions.assertEquals(SolverStatus.UNSAT, solver.status)
      val sw = com.google.common.base.Stopwatch.createStarted()
      val itp = solver.getInterpolant(pattern)
      sw.stop()

      println("$name: ${itp.eval(A)} (${sw.elapsed(TimeUnit.MILLISECONDS)} ms)")
    }
  }

  @Test
  fun testEasyLIA() {
    for ((name, solver) in solvers) {
      val A = solver.createMarker()
      val B = solver.createMarker()
      val pattern = solver.createBinPattern(A, B)

      solver.add(A, Eq(Mod(b!!, Int(2)), Int(0)))
      solver.add(A, Eq(Add(b!!, Int(1)), a!!))
      solver.add(B, Eq(Mod(a!!, Int(2)), Int(0)))

      solver.check()
      Assertions.assertEquals(SolverStatus.UNSAT, solver.status)
      val sw = com.google.common.base.Stopwatch.createStarted()
      val itp = solver.getInterpolant(pattern)
      sw.stop()

      println("$name: ${itp.eval(A)} (${sw.elapsed(TimeUnit.MILLISECONDS)} ms)")
    }
  }

  @Test
  fun testPushPop() {
    for ((name, solver) in solvers) {
      val A = solver.createMarker()
      val B = solver.createMarker()
      val pattern = solver.createBinPattern(A, B)

      solver.add(A, Eq(a, b))
      solver.add(B, Eq(b, c))

      solver.push()

      solver.add(A, Neq(a, c))
      solver.check()
      Assertions.assertEquals(SolverStatus.UNSAT, solver.status)

      solver.pop()

      solver.add(B, Neq(a, c))
      solver.check()
      Assertions.assertEquals(SolverStatus.UNSAT, solver.status)
      val sw = com.google.common.base.Stopwatch.createStarted()
      val itp = solver.getInterpolant(pattern)
      sw.stop()

      println("$name: ${itp.eval(A)} (${sw.elapsed(TimeUnit.MILLISECONDS)} ms)")
    }
  }
}
