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
import hu.bme.mit.theta.analysis.zone.ZonePrec
import hu.bme.mit.theta.analysis.zone.ZoneState
import hu.bme.mit.theta.core.clock.constr.ClockConstrs.Eq
import hu.bme.mit.theta.core.clock.op.GuardOp
import hu.bme.mit.theta.core.clock.op.ResetOp
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.model.ClockDelayLabel
import hu.bme.mit.theta.xcfa.model.ClockOpLabel
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import java.util.Collections

class XcfaZoneInvTransFunc : InvTransFunc<ZoneState, XcfaAction, ZonePrec> {

  override fun getPreStates(state: ZoneState, action: XcfaAction, prec: ZonePrec): Collection<ZoneState> {
    val preZoneBuilder = state.project(prec.vars)
    action.label.getFlatLabels().reversed().forEach { label ->
      when (label) {
        is ClockDelayLabel -> preZoneBuilder.down()
        is ClockOpLabel -> label.op.let { op ->
          when (op) {
            is GuardOp -> {
              preZoneBuilder.and(op.constr)
            }
            is ResetOp -> {
              preZoneBuilder
                .and(Eq(op.`var`, op.value))
                .free(op.`var`)
            }
            else -> error("Unexpected clock op: $op")
          }
        }
        else -> error("Unexpected label $label")
      }
    }
    preZoneBuilder.nonnegative()
    return Collections.singleton(preZoneBuilder.build())
  }
}
