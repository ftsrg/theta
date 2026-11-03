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
package hu.bme.mit.theta.xcfa.cli.checkers

import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.pred.PredState
import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.ImmutableValuation
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.xcfa.analysis.XcfaProcessState
import hu.bme.mit.theta.xcfa.model.EmptyMetaData
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import java.util.LinkedList
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test

class ThreadLocalProofTest {
  private val parameter = Var("__theta_mutex_tid", Int())
  private val first = Var("T1::__theta_mutex_tid", Int())
  private val second = Var("T2::__theta_mutex_tid", Int())
  private val values = ImmutableValuation.builder().put(first, Int(1)).put(second, Int(2)).build()

  private fun process(instance: VarDecl<IntType>) =
    XcfaProcessState(
      LinkedList(listOf(XcfaLocation("shared_location", metadata = EmptyMetaData))),
      LinkedList(listOf(mapOf(parameter to instance))),
    )

  @Test
  fun explicitProofKeepsEachThreadsParameterValue() {
    val state = ExplState.of(values)
    val firstProof = generalizeProofState(state, process(first)) as ExplState
    val secondProof = generalizeProofState(state, process(second)) as ExplState
    assertEquals(Int(1), firstProof.`val`.eval(parameter).get())
    assertEquals(Int(2), secondProof.`val`.eval(parameter).get())
  }

  @Test
  fun predicateProofDoesNotMergeDifferentThreadIdsIntoAContradiction() {
    val state = PredState.of(Eq(first.ref, Int(1)), Eq(second.ref, Int(2)))
    for ((instance, id) in listOf(first to 1, second to 2)) {
      val generalized = generalizeProofState(state, process(instance)) as PredState
      val valuation =
        ImmutableValuation.builder()
          .put(first, Int(1))
          .put(second, Int(2))
          .put(parameter, Int(id))
          .build()
      assertEquals(True(), generalized.toExpr().eval(valuation))
    }
  }
}
