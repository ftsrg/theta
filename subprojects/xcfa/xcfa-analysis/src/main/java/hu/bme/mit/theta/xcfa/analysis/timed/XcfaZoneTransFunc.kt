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

import hu.bme.mit.theta.analysis.TransFunc
import hu.bme.mit.theta.analysis.zone.ZonePrec
import hu.bme.mit.theta.analysis.zone.ZoneState
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.getFlatLabels
import hu.bme.mit.theta.xcfa.model.ClockDelayLabel
import hu.bme.mit.theta.xcfa.model.ClockOpLabel
import java.util.Collections

class XcfaZoneTransFunc : TransFunc<ZoneState, XcfaAction, ZonePrec> {

    override fun getSuccStates(state: ZoneState, action: XcfaAction, prec: ZonePrec): Collection<ZoneState> {
        val succZoneBuilder = state
            .project(prec.vars)
            .nonnegative()
        action.label.getFlatLabels().forEach {
            when (it) {
                is ClockDelayLabel -> succZoneBuilder.up()
                is ClockOpLabel -> succZoneBuilder.execute(it.op)
                else -> error("Unexpected label ${action.label}")
            }
        }
        return Collections.singleton(succZoneBuilder.build())
    }
}
