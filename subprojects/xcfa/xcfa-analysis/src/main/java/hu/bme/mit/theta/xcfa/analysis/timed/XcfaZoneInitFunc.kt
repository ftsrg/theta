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

import hu.bme.mit.theta.analysis.InitFunc
import hu.bme.mit.theta.analysis.zone.ZonePrec
import hu.bme.mit.theta.analysis.zone.ZoneState
import hu.bme.mit.theta.core.clock.constr.TrueConstr
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import java.util.Collections

class XcfaZoneInitFunc(private val initLocs : Collection<XcfaLocation>) : InitFunc<ZoneState, ZonePrec> {

    override fun getInitStates(prec: ZonePrec): Collection<ZoneState> {
        val initZoneBuilder = ZoneState.zero(prec.vars).transform()
            .up()
        initLocs
            .map { it.invariant }
            .filter { it !is TrueConstr }
            .fold(
                initZoneBuilder,
                { builder, invariant -> builder.and(invariant) }
            )
        return Collections.singleton(initZoneBuilder.build())
    }
}
