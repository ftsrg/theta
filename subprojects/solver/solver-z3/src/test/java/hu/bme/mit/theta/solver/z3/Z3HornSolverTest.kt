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
package hu.bme.mit.theta.solver.z3

import hu.bme.mit.theta.common.OsHelper
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
import hu.bme.mit.theta.solver.HornSolver
import java.util.stream.Stream
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Assumptions
import org.junit.jupiter.api.BeforeEach
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.MethodSource

class Z3HornSolverTest {
  companion object {

    @JvmStatic
    fun solvers(): Stream<Arguments> {
      return Stream.of(Arguments.of(Z3SolverFactory.getInstance().createHornSolver()))
    }
  }

  @BeforeEach
  fun before() {
    Assumptions.assumeTrue(OsHelper.getOs() == OsHelper.OperatingSystem.LINUX)
  }

  @ParameterizedTest
  @MethodSource("solvers")
  fun testSolvable(solver: HornSolver) {
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

      val checkerSolver = Z3SolverFactory.getInstance().createSolver()
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
      }
    }
  }

  @ParameterizedTest
  @MethodSource("solvers")
  fun testUnsolvable(solver: HornSolver) {
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
    }
  }

  @ParameterizedTest
  @MethodSource("solvers")
  fun testNonlinearUnsolvable(solver: HornSolver) {
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
    }
  }
}
