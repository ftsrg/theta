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

import hu.bme.mit.theta.common.OsHelper
import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.core.ParamHolder
import hu.bme.mit.theta.core.Relation
import hu.bme.mit.theta.core.decl.Decls.Const
import hu.bme.mit.theta.core.plus
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.*
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.functype.FuncExprs.App
import hu.bme.mit.theta.core.type.functype.FuncLitExpr
import hu.bme.mit.theta.core.type.functype.FuncType
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.solver.smtlib.solver.installer.SmtLibSolverInstallerException
import org.junit.jupiter.api.*
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.MethodSource

class GenericSmtLibHornSolverTest {
  companion object {

    private var solverManager: SmtLibSolverManager? = null
    private val solverFactories: MutableMap<Pair<String, String>, SolverFactory> = LinkedHashMap()

    private val SOLVERS: List<Pair<String, String>> =
      listOf(
        Pair("z3", "4.13.0"),
        Pair("z3", "4.12.6"),
        Pair("eldarica", "2.1"),
        Pair("golem", "0.5.0"),
      )

    @JvmStatic
    fun solvers(): List<Arguments> {
      return SOLVERS.map { Arguments.of(it) }
    }

    @BeforeAll
    @JvmStatic
    fun init() {
      if (OsHelper.getOs() == OsHelper.OperatingSystem.LINUX) {
        val home = SmtLibSolverManager.HOME

        solverManager = SmtLibSolverManager.create(home, NullLogger.getInstance())
        for ((solver, version) in SOLVERS) {

          try {
            solverManager!!.install(solver, version, version, null, false)
          } catch (e: SmtLibSolverInstallerException) {
            e.printStackTrace()
          }

          solverFactories.put(
            Pair(solver, version),
            solverManager!!.getSolverFactory(solver, version),
          )
        }
      }
    }

    @AfterAll
    @JvmStatic
    fun destroy() {
      for ((solver, version) in SOLVERS) {
        try {
          solverManager?.uninstall(solver, version)
        } catch (e: SmtLibSolverInstallerException) {
          e.printStackTrace()
        }
      }
    }
  }

  @BeforeEach
  fun before() {
    Assumptions.assumeTrue(OsHelper.getOs() == OsHelper.OperatingSystem.LINUX)
  }

  @ParameterizedTest(name = "[{index}] {0}")
  @MethodSource("solvers")
  fun testSolvable(name: Pair<String, String>) {
    val solverFactory = solverFactories[name]!!
    val solver = solverFactory.createHornSolver()
    solver.use { hornSolver ->
      val p = ParamHolder(Int())
      val init = Relation("init", Int(), Int())
      val inv = Relation("inv", Int(), Int())

      init(p[0], p[1]) += Eq(p[0], Int(0)) + Eq(p[1], Int(1))
      inv(p[0], p[1]) += init(p[0], p[1]).expr
      inv(p[0], p[2]) += inv(p[0], p[1]).expr + Eq(p[2], Add(p[1], Int(1)))

      !(inv(p[0], p[1]) with Lt(p[1], Int(1)))

      hornSolver.add(init)
      hornSolver.add(inv)

      val status = hornSolver.check()
      Assertions.assertTrue(status.isSat)
      val model = hornSolver.model.toMap()

      Assertions.assertTrue(model.containsKey(inv.constDecl))
      Assertions.assertTrue(model.containsKey(init.constDecl))

      val checkerSolver =
        solverFactories.filter { it.key.first.equals("z3") }.values.first().createSolver()
      checkerSolver.use {
        val p0 = Const("p0", Int())
        val p1 = Const("p1", Int())
        checkerSolver.add(
          App(
            App(
              model.get(init.constDecl) as FuncLitExpr<IntType, FuncType<IntType, BoolType>>,
              p0.ref,
            ),
            p1.ref,
          )
        )

        checkerSolver.add(Lt(p1.ref, Int(0)))
        Assertions.assertTrue(checkerSolver.check().isUnsat)
        System.err.println(model.toMap())
      }
    }
  }

  @ParameterizedTest(name = "[{index}] {0}")
  @MethodSource("solvers")
  fun testUnsolvable(name: Pair<String, String>) {
    val solverFactory = solverFactories[name]!!
    val solver = solverFactory.createHornSolver()

    solver.use { hornSolver ->
      val p = ParamHolder(Int())
      val init = Relation("init", Int(), Int())
      val inv = Relation("inv", Int(), Int())

      init(p[0], p[1]) += Eq(p[0], Int(0)) + Eq(p[1], Int(1))
      inv(p[0], p[1]) += init(p[0], p[1]).expr
      inv(p[0], p[2]) += inv(p[0], p[1]).expr + Eq(p[2], Add(p[1], Int(1)))

      !(inv(p[0], p[1]) with Leq(p[1], Int(1)))

      hornSolver.add(init)
      hornSolver.add(inv)

      val status = hornSolver.check()
      Assertions.assertTrue(status.isUnsat)

      val proof = hornSolver.proof
      Assertions.assertTrue(proof != null)
      System.err.println(proof)
    }
  }

  @ParameterizedTest(name = "[{index}] {0}")
  @MethodSource("solvers")
  fun testNonlinearUnsolvable(name: Pair<String, String>) {
    val solverFactory = solverFactories[name]!!
    val solver = solverFactory.createHornSolver()

    solver.use { hornSolver ->
      val p = ParamHolder(Int())
      val init1 = Relation("init1", Int(), Int())
      val init2 = Relation("init2", Int(), Int())
      val inv1 = Relation("inv1", Int(), Int())
      val inv2 = Relation("inv2", Int(), Int())

      val err = Relation("err", Int(), Int())

      init1(p[0], p[1]) += Eq(p[0], Int(0)) + Eq(p[1], Int(0))
      init2(p[0], p[1]) += Eq(p[0], Int(0)) + Eq(p[1], Int(0))
      inv1(p[0], p[1]) += init1(p[0], p[1]).expr
      inv1(p[0], p[2]) += inv1(p[0], p[1]).expr + Eq(p[2], Add(p[1], Int(3)))
      inv2(p[0], p[1]) += init2(p[0], p[1]).expr
      inv2(p[0], p[2]) += inv2(p[0], p[1]).expr + Eq(p[2], Add(p[1], Int(5)))

      err(p[0], p[2]) += inv1(p[0], p[1]).expr + inv2(p[0], p[1]).expr + Gt(p[1], Int(0))

      !err(p[0], p[1])

      hornSolver.add(init1)
      hornSolver.add(init2)
      hornSolver.add(inv1)
      hornSolver.add(inv2)
      hornSolver.add(err)

      val status = hornSolver.check()
      Assertions.assertTrue(status.isUnsat)

      val proof = hornSolver.proof
      Assertions.assertTrue(proof != null)
      System.err.println(proof)
    }
  }
}
