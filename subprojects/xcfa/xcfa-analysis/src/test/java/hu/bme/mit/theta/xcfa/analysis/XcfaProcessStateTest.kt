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

import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.xcfa.model.EmptyMetaData
import hu.bme.mit.theta.xcfa.model.NopLabel
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import java.util.LinkedList
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test

class XcfaProcessStateTest {

  private val x = Var("x", Int())
  private val callerLookup: Map<VarDecl<*>, VarDecl<*>> = mapOf(x to Var("T0::_::x", Int()))
  private val calleeLookup: Map<VarDecl<*>, VarDecl<*>> = mapOf(x to Var("T0::P1::x", Int()))
  private val caller = XcfaLocation("caller", metadata = EmptyMetaData)
  private val callee = XcfaLocation("callee", metadata = EmptyMetaData)

  @Test
  fun poppingACoveredCallLeavesTheCallersFrameOnTop() {
    val lookups = LinkedList(listOf(calleeLookup, callerLookup))
    val state =
      XcfaProcessState(
        LinkedList(listOf(callee, caller)),
        lookups,
        returnStmts = LinkedList(listOf(NopLabel, NopLabel)),
      )
    state.popCovered()
    assertEquals(callee, state.popped)
    assertEquals(listOf(caller), state.locs.toList())
    assertEquals(callerLookup, state.varLookup.peek())
    assertEquals(1, state.returnStmts.size)
    // the stack it shared with its parent state stays as it was
    assertEquals(2, lookups.size)
  }
}
