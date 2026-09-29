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
package hu.bme.mit.theta.analysis.algorithm.bounded.pipeline

import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.InvariantProof
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.constraints.VariableConsistencyMEPassValidator
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.exception.MEPassPipelineException
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.ImmutableValuation
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import java.time.Duration
import org.junit.jupiter.api.Assertions.assertThrows
import org.junit.jupiter.api.Assertions.assertTimeoutPreemptively
import org.junit.jupiter.api.Test

class VariableConsistencyMEPassValidatorTest {

  private fun vars(n: Int): List<VarDecl<*>> = (0 until n).map { Var("v$it", Int()) }

  /** A pass whose input model has [upstreamVars], answered backward with a cex over [cexVars]. */
  private fun steps(
    upstreamVars: List<VarDecl<*>>,
    cexVars: List<VarDecl<*>>,
  ): List<PipelineStep<InvariantProof>> {
    val model = MonolithicExpr(True(), True(), True(), vars = upstreamVars)
    val valuation = ImmutableValuation.builder().also { b -> cexVars.forEach { b.put(it, Int(0)) } }
    val state = ExplState.of(valuation.build())
    val cex = Trace.of<ExplState, ExprAction>(listOf(state), listOf())
    val result = SafetyResult.unsafe<InvariantProof, Trace<ExplState, ExprAction>>(cex, state)
    return listOf(0 to MonolithicExprPassResult(model), 1 to MonolithicExprPassResult(result))
  }

  @Test
  fun `cex over the upstream variables is accepted on a large model`() {
    val vars = vars(200_000)
    val steps = steps(vars, vars)
    assertTimeoutPreemptively(Duration.ofSeconds(2)) {
      VariableConsistencyMEPassValidator.checkStepResult(steps)
    }
  }

  @Test
  fun `cex over a foreign variable is rejected`() {
    val vars = vars(3)
    val steps = steps(vars.take(2), vars)
    assertThrows(MEPassPipelineException::class.java) {
      VariableConsistencyMEPassValidator.checkStepResult(steps)
    }
  }
}
