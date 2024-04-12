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

package hu.bme.mit.theta.xcfa.analysis.oc

import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.XcfaBuilder
import hu.bme.mit.theta.xcfa.model.XcfaProcedureBuilder
import hu.bme.mit.theta.xcfa.passes.ProcedurePass
import hu.bme.mit.theta.xcfa.passes.ProcedurePassManager

internal fun XCFA.optimizeFurther(passes: List<ProcedurePass>): XCFA {
    if (passes.isEmpty()) return this
    val passManager = ProcedurePassManager(passes)
    val copy: XcfaProcedureBuilder.() -> XcfaProcedureBuilder = {
        XcfaProcedureBuilder(
            name = name,
            manager = passManager,
            params = getParams().toMutableList(),
            vars = getVars().toMutableSet(),
            locs = getLocs().toMutableSet(),
            edges = getEdges().toMutableSet(),
            metaData = metaData.toMutableMap()
        ).also { it.copyMetaLocs(this) }
    }

    val builder = XcfaBuilder(name, vars.toMutableSet())
    procedureBuilders.forEach { builder.addProcedure(it.copy()) }
    initProcedureBuilders.forEach { (proc, params) ->
        val initProc = builder.getProcedures().find { it.name == proc.name } ?: proc.copy()
        builder.addEntryPoint(initProc, params)
    }
    return builder.build()
}