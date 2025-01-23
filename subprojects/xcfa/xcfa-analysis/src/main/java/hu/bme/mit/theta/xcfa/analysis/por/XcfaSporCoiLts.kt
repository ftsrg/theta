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
package hu.bme.mit.theta.xcfa.analysis.por

import hu.bme.mit.theta.analysis.LTS
import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.analysis.coi.transFuncVersion
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.XcfaEdge

class XcfaSporCoiLts(xcfa: XCFA, coiLTS: LTS<XcfaState<out PtrState<out ExprState>>, XcfaAction>) :
  XcfaSporLts(xcfa) {

  init {
    simpleXcfaLts = coiLTS
  }

  override fun <P : Prec?> getEnabledActionsFor(
    state: XcfaState<out PtrState<*>>,
    exploredActions: Collection<XcfaAction>,
    prec: P,
  ): Set<XcfaAction> {
    return getEnabledActionsFor(
      state,
      simpleXcfaLts.getEnabledActionsFor(state, exploredActions, prec),
    )
  }

  override fun getEdge(action: XcfaAction): XcfaEdge =
    super.getEdge(action.transFuncVersion ?: action)
}
