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
package hu.bme.mit.theta.xcfa.analysis

import hu.bme.mit.theta.analysis.expl.ExplPrec
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.model.ImmutableValuation
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.xcfa.model.EmptyMetaData
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import java.util.LinkedList
import org.junit.jupiter.api.Assertions.assertFalse
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

class XcfaPrecTest {

  private val x = Var("x", Int())
  private val caller = XcfaLocation("caller", metadata = EmptyMetaData)
  private val callee = XcfaLocation("callee", metadata = EmptyMetaData)
  private val other = XcfaLocation("other", metadata = EmptyMetaData)

  private fun state(value: Int, vararg stack: XcfaLocation) =
    XcfaState(
      null,
      mapOf(0 to XcfaProcessState(LinkedList(stack.toList()), LinkedList())),
      ExplState.of(ImmutableValuation.builder().put(x, Int(value)).build()),
    )

  @Test
  fun noPopMatchesTheCallStackWhateverTheData() {
    val prec = XcfaPrec(ExplPrec.empty(), mutableListOf(state(1, callee, caller)))
    assertTrue(prec.noPop(state(2, callee, caller)))
    assertFalse(prec.noPop(state(1, other, caller)))
    assertFalse(prec.noPop(state(1, callee)))
  }

  @Test
  fun refiningTheInnerPrecisionKeepsNoPop() {
    val prec = XcfaPrec(ExplPrec.empty(), mutableListOf(state(1, callee, caller)))
    val refined = prec.refine(ExplPrec.of(listOf(x)))
    assertTrue(refined.noPop(state(1, callee, caller)))
  }
}
