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

package hu.bme.mit.theta.xcfa.analysis.timed

import hu.bme.mit.theta.analysis.InvTransFunc
import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.State
import hu.bme.mit.theta.analysis.TransFunc
import hu.bme.mit.theta.analysis.prod2.ActionSplitter
import hu.bme.mit.theta.common.Tuple2
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.model.ClockDelayLabel
import hu.bme.mit.theta.xcfa.model.ClockOpLabel
import hu.bme.mit.theta.xcfa.model.SequenceLabel
import hu.bme.mit.theta.xcfa.utils.getFlatLabels

object DataClockXcfaActionSplitter : ActionSplitter<XcfaAction> {

    private val actionPartitions by lazy {
      mutableMapOf<XcfaAction, Tuple2<XcfaAction, XcfaAction>>()
    }

    override fun apply(action: XcfaAction): Tuple2<XcfaAction, XcfaAction> {
      return actionPartitions.computeIfAbsent(action, { action ->
        val (dataAction, clockAction) = action.label.getFlatLabels()
          .partition { it !is ClockOpLabel && it !is ClockDelayLabel }
          .toList()
          .map { separatedLabels ->
            action.withLabel(SequenceLabel(separatedLabels, action.label.metadata))
          }
        Tuple2.of(dataAction, clockAction)
      })
    }

    fun getClockAction(action: XcfaAction) : XcfaAction = apply(action).get2()

    fun <S : State, P : Prec> getClockActionTransFunc(transFunc : TransFunc<S, XcfaAction, P>) = {
        s : S, a : XcfaAction, p : P -> transFunc.getSuccStates(s, getClockAction(a), p)
    }

    fun <S : State, P : Prec> getClockActionInvTransFunc(invTransFunc : InvTransFunc<S, XcfaAction, P>) = {
        s : S, a : XcfaAction, p : P -> invTransFunc.getPreStates(s, getClockAction(a), p)
    }
}
