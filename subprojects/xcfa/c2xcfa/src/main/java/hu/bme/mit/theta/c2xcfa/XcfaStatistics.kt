/*
 *  Copyright 2023 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.c2xcfa

import hu.bme.mit.theta.xcfa.collectHavocs
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.XcfaBuilder

data class XcfaStatistics(
    val globalVars: Int,
    val procedures: Collection<XcfaProcedureStatistics>
)

data class XcfaProcedureStatistics(
    val localVariables: Int,
    val locations: Int,
    val edges: Int,
    val havocs: Int,
    val cyclComplexity: Int,
    val hasFinalLoc: Boolean,
)

fun XCFA.getStatistics(): XcfaStatistics {
    return XcfaStatistics(
        globalVars = vars.size,
        procedures = procedures.map {
            XcfaProcedureStatistics(
                localVariables = it.vars.size,
                locations = it.locs.size,
                edges = it.edges.size,
                havocs = it.edges.map { it.label.collectHavocs().size }.reduce(Int::plus),
                cyclComplexity = it.edges.size - it.locs.size + 2,
                hasFinalLoc = it.finalLoc.isPresent
            )
        }
    )
}

fun XcfaBuilder.getStatistics(): XcfaStatistics {
    return XcfaStatistics(
        globalVars = this.getVars().size,
        procedures = getProcedures().map {
            XcfaProcedureStatistics(
                localVariables = it.getVars().size,
                locations = it.getLocs().size,
                edges = it.getEdges().size,
                havocs = it.getEdges().map { it.label.collectHavocs().size }.reduce(Int::plus),
                cyclComplexity = it.getEdges().size - it.getLocs().size + 2,
                hasFinalLoc = it.finalLoc.isPresent
            )
        }
    )
}