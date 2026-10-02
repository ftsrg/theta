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

package hu.bme.mit.theta.xcfa.analysis.lazy

import hu.bme.mit.theta.analysis.algorithm.lazy.InitAbstractor
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.xcfa.analysis.XcfaState

class XcfaInitAbstractor<SConcr: ExprState, SAbstr: ExprState>(
  private val initAbstractor : InitAbstractor<SConcr, SAbstr>
) : InitAbstractor<XcfaState<PtrState<SConcr>>, XcfaState<PtrState<SAbstr>>> {

  override fun getInitAbstrState(state: XcfaState<PtrState<SConcr>>) : XcfaState<PtrState<SAbstr>> {
    val concrPtrState = state.sGlobal
    val concrState = concrPtrState.innerState
    val abstrState = initAbstractor.getInitAbstrState(concrState)
    val abstrPtrState = PtrState(
      innerState = abstrState,
      nextCnt = concrPtrState.nextCnt
    )
    return XcfaState(
      state.xcfa,
      state.processes,
      abstrPtrState,
      state.mutexes,
      state.threadLookup,
      state.bottom,
    )
  }
}
