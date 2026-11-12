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

import hu.bme.mit.theta.frontend.transformation.grammar.preprocess.ArithmeticTrait.BITWISE
import hu.bme.mit.theta.frontend.transformation.grammar.preprocess.ArithmeticTrait.FLOAT
import hu.bme.mit.theta.frontend.transformation.grammar.preprocess.ArithmeticTrait.NONCONST_DIV
import hu.bme.mit.theta.frontend.transformation.grammar.preprocess.ArithmeticTrait.NONLIN_INT
import hu.bme.mit.theta.xcfa.cli.checkers.forArithmetic
import hu.bme.mit.theta.xcfa.cli.params.DssConfig
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test

class DssNonlinearSolverTest {

  private val config =
    DssConfig(solver = "JavaSMT:MATHSAT5", fallbackSolver = "Z3", nonlinearSolver = "Z3:new")

  @Test
  fun `the nonlinear solver takes over pure nonlinear integer programs`() {
    for (traits in listOf(setOf(NONLIN_INT), setOf(NONLIN_INT, NONCONST_DIV))) {
      val chosen = config.forArithmetic(traits)
      assertEquals("Z3:new", chosen.solver)
      assertEquals("JavaSMT:MATHSAT5", chosen.fallbackSolver)
    }
  }

  @Test
  fun `other programs keep the configured solvers`() {
    for (traits in listOf(setOf(), setOf(FLOAT, NONLIN_INT), setOf(BITWISE, NONLIN_INT))) {
      assertEquals(config, config.forArithmetic(traits))
    }
    val plain = config.copy(nonlinearSolver = null)
    assertEquals(plain, plain.forArithmetic(setOf(NONLIN_INT)))
  }
}
