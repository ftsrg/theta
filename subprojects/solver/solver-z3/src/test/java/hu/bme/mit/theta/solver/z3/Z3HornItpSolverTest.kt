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

import hu.bme.mit.theta.core.decl.ConstDecl
import hu.bme.mit.theta.core.decl.Decls.Const
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.*
import hu.bme.mit.theta.core.type.booltype.BoolExprs.*
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.solver.HornItpSolver
import java.util.stream.Stream
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.MethodSource

class Z3HornItpSolverTest {
  companion object {

    @JvmStatic
    fun solvers(): Stream<Arguments> {
      return Stream.of(
        Arguments.of(
          HornItpSolver(
            Z3SolverFactory.getInstance().createSolver(),
            Z3SolverFactory.getInstance().createHornSolver(),
          )
        )
      )
    }

    private val constMap = mutableMapOf<Pair<String, Type>, ConstDecl<*>>()

    private fun cachingConst(name: String, type: Type) =
      constMap.computeIfAbsent(Pair(name, type)) { (name, type) -> Const(name, type) }
  }

  @ParameterizedTest
  @MethodSource("solvers")
  fun testBinaryItp(solver: HornItpSolver) {
    solver.use { hornSolver ->
      val a =
        And(
          Lt(cachingConst("b", Int()).ref, cachingConst("a", Int()).ref),
          Eq(cachingConst("b", Int()).ref, Int(0)),
        )
      val b = Gt(Int(0), cachingConst("a", Int()).ref)

      val marker1 = hornSolver.createMarker()
      val marker2 = hornSolver.createMarker()
      val pattern = solver.createBinPattern(marker1, marker2)

      hornSolver.add(marker1, a)
      hornSolver.add(marker2, b)

      val status = hornSolver.check()
      Assertions.assertTrue(status.isUnsat)

      val itp = hornSolver.getInterpolant(pattern)

      Assertions.assertTrue(
        (ExprUtils.getConstants(itp.eval(marker1)) - cachingConst("a", Int())).isEmpty()
      )

      Z3SolverFactory.getInstance().createSolver().use {
        it.push()
        it.add(Not(Imply(a, itp.eval(marker1))))
        Assertions.assertTrue(it.check().isUnsat)
        it.pop()

        it.push()
        it.add(b)
        it.add(itp.eval(marker1))
        Assertions.assertTrue(it.check().isUnsat)
        it.pop()
      }
    }
  }
}
