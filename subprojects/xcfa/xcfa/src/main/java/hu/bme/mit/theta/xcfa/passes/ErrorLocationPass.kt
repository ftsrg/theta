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

import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.xcfa.model.*

/**
 * Transforms all procedure calls to designated error procedures into edges to error locations.
 * Requires the ProcedureBuilder be `deterministic`.
 */
class ErrorLocationPass(val checkOverflow: Boolean, val parseContext: ParseContext) : ProcedurePass {

    override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
        checkNotNull(builder.metaData["deterministic"])
        for (edge in ArrayList(builder.getEdges())) {
            val edges = edge.splitIf(this::predicate)
            if (edges.size > 1 || (edges.size == 1 && predicate(
                    (edges[0].label as SequenceLabel).labels[0]))) {
                builder.removeEdge(edge)
                edges.forEach {
                    if (predicate((it.label as SequenceLabel).labels[0])) {
                        if (builder.errorLoc.isEmpty) builder.createErrorLoc()
                        builder.addEdge(
                            XcfaEdge(it.source, builder.errorLoc.get(), SequenceLabel(listOf())))
                    } else {
                        builder.addEdge(it)
                    }
                }
            }
        }
        return builder
    }

    private fun predicate(it: XcfaLabel): Boolean {
        return it is InvokeLabel && it.name.equals(if (checkOverflow) "overflow" else "reach_error")
    }
}