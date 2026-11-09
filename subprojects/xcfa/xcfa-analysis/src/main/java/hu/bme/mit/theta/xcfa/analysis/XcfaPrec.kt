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

import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.xcfa.model.XcfaLocation

/**
 * [noPop]: states whose call stack must not be popped by abstract stack covering. A state matches
 * by its call stacks alone ([callStacks]), not by its data: an exact match would hold for one
 * valuation only, so CEGAR would learn one state per iteration and not converge.
 */
data class XcfaPrec<P : Prec>(val p: P, val noPop: MutableList<XcfaState<*>> = mutableListOf()) :
  Prec {

  fun noPop(state: XcfaState<*>): Boolean = noPop.any { it.callStacks() == state.callStacks() }

  override fun getUsedVars(): Collection<VarDecl<*>> {
    return p.usedVars
  }

  fun refine(runningPrec: P): XcfaPrec<P> {
    return if (this.p == runningPrec) {
      this
    } else {
      // the stacks learned not to pop do not depend on the inner precision
      XcfaPrec(runningPrec, noPop.toMutableList())
    }
  }
}

fun XcfaState<*>.callStacks(): Map<Int, List<XcfaLocation>> =
  processes.mapValues { it.value.locs.toList() }
