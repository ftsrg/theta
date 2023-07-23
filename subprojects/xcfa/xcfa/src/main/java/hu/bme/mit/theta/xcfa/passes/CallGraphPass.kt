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

package hu.bme.mit.theta.xcfa.passes

import hu.bme.mit.theta.xcfa.getFlatLabels
import hu.bme.mit.theta.xcfa.model.InvokeLabel
import hu.bme.mit.theta.xcfa.model.StartLabel
import hu.bme.mit.theta.xcfa.model.XcfaProcedureBuilder

/**
 * Mark procedure builders with reachability info.
 * Marks the called ProcedureBuilders `reachable-from-<X>`.
 */
class CallGraphPass : ProcedurePass {

    override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
        val calledProcedures = LinkedHashSet<String>()
        builder.getEdges().map { it.getFlatLabels().filter { it is InvokeLabel || it is StartLabel } }.flatten()
            .forEach {
                when (it) {
                    is InvokeLabel -> calledProcedures.add(it.name)
                    is StartLabel -> calledProcedures.add(it.name)
                    else -> error("Will never be here (due to filter above)")
                }
            }
        builder.parent.getProcedures().filter { calledProcedures.contains(it.name) }
            .forEach { it.metaData["reachable-from-${builder.name}"] = Unit }
        return builder
    }
}