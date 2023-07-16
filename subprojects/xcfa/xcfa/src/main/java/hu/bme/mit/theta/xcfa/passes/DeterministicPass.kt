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
import hu.bme.mit.theta.xcfa.model.NondetLabel
import hu.bme.mit.theta.xcfa.model.XcfaProcedureBuilder

/**
 * This pass converts all edges to a deterministic normal form, i.e., no NonDetLabels can be found on the edges.
 * Requires the ProcedureBuilder to be `normal` (@see NormalizePass)
 * Sets the `deterministic` flag on the ProcedureBuilder
 */

class DeterministicPass(val parseContext: ParseContext) : ProcedurePass {

    override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
        checkNotNull(builder.metaData["normal"])
        val edges = LinkedHashSet(builder.getEdges())
        for (edge in edges) {
            if (edge.label is NondetLabel) {
                builder.removeEdge(edge)
                for (label in edge.label.labels) {
                    builder.addEdge(edge.withLabel(label))
                }
            }
        }
        builder.metaData["deterministic"] = Unit
        return builder
    }
}