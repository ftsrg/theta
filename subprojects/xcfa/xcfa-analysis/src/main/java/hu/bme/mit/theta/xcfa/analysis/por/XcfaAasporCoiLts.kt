/*
 *  Copyright 2024 Budapest University of Technology and Economics
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
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.analysis.coi.transFuncVersion
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.XcfaEdge

class XcfaAasporCoiLts(
    xcfa: XCFA,
    ignoredVarRegistry: MutableMap<Decl<out Type>, MutableSet<ExprState>>,
    coiLTS: LTS<XcfaState<*>, XcfaAction>
) : XcfaAasporLts(xcfa, ignoredVarRegistry) {

    init {
        simpleXcfaLts = coiLTS
    }

    override fun getEdgeOf(action: XcfaAction): XcfaEdge =
        super.getEdgeOf(action.transFuncVersion ?: action)

    override fun isBackwardAction(action: XcfaAction): Boolean =
        backwardTransitions.any { it.source == action.edge.source && it.target == action.edge.target }
}