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
 * Removes edges that only contain NopLabels (possibly nested)
 */

class EmptyEdgeRemovalPass(val parseContext: ParseContext) : ProcedurePass {

    override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
        while (true) {
            val edge = builder.getEdges()
                .find { it.label.isNop() && !it.target.error && !it.target.final && !it.source.initial }
                ?: return builder
            builder.removeEdge(edge)
            if (edge.source != edge.target) {
                val incomingEdges = ArrayList(edge.source.incomingEdges)
                incomingEdges.forEach { builder.removeEdge(it) }
                incomingEdges.forEach { builder.addEdge(it.withTarget(edge.target)) }
            }
        }
    }

    private fun XcfaLabel.isNop(): Boolean =
        when (this) {
            is NondetLabel -> labels.all { it.isNop() }
            is SequenceLabel -> labels.all { it.isNop() }
            is NopLabel -> true
            else -> false
        }
}