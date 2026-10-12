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
package hu.bme.mit.theta.xcfa.cli.utils

import hu.bme.mit.theta.analysis.Action
import hu.bme.mit.theta.analysis.State
import hu.bme.mit.theta.analysis.algorithm.arg.ArgNode
import hu.bme.mit.theta.analysis.algorithm.arg.ArgNodeComparators.ArgNodeComparator
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.prod2.Prod2State
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.xcfa.ThetaHelperDeclarations.Witness.SEGMENT_COUNTER
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import java.math.BigInteger

/**
 * Orders ArgNodes by the explicit value of the witness-instrumentation segment counter
 * ([SEGMENT_COUNTER]). A node whose abstract state pins the counter to a concrete value is explored
 * before a node where the counter is still abstract, and among the pinned ones the *highest*
 * counter is explored first -- this drives the search forward along the witness segment progression
 * while the remaining nodes are handled in the (BFS) order supplied by the combined fallback
 * comparator.
 *
 * "Less" means "removed from the waitlist (explored) earlier".
 */
class XcfaSegmentOrderComparator : ArgNodeComparator {

  override fun compare(
    n1: ArgNode<out State, out Action>,
    n2: ArgNode<out State, out Action>,
  ): Int {
    val v1 = segmentValue(n1)
    val v2 = segmentValue(n2)
    return when {
      v1 != null && v2 != null -> v2.compareTo(v1) // higher counter first
      v1 != null -> -1 // pinned counter before abstract counter
      v2 != null -> 1
      else -> 0 // both abstract: defer to the fallback comparator
    }
  }

  private fun segmentValue(node: ArgNode<out State, out Action>): BigInteger? =
    extractSegmentCounter(node.state)

  /**
   * Descends through the known state wrappers ([XcfaState] -> [PtrState] -> [Prod2State]) until a
   * [Valuation] that explicitly assigns [SEGMENT_COUNTER] is found, returning its concrete value
   * (or null if no component pins the counter).
   */
  private fun extractSegmentCounter(state: Any?): BigInteger? =
    when (state) {
      is XcfaState<*> -> extractSegmentCounter(state.sGlobal)
      is PtrState<*> -> extractSegmentCounter(state.innerState)
      is Prod2State<*, *> ->
        extractSegmentCounter(state.state1) ?: extractSegmentCounter(state.state2)
      is Valuation ->
        state
          .toMap()
          .entries
          .firstOrNull { it.key.name == SEGMENT_COUNTER }
          ?.let { (it.value as? IntLitExpr)?.value }
      is ExprState -> null
      else -> null
    }

  override fun toString(): String = javaClass.simpleName

  companion object {
    private const val serialVersionUID = 1L
  }
}
