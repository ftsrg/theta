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
 * This pass converts all edges to a normalized form, i.e., the outermost label is a NonDetLabel containing
 * SequenceLabels, which do not contain any more Sequence or NonDet labels.
 * Sets the `normal` flag on the ProcedureBuilder
 */

class NormalizePass(val parseContext: ParseContext) : ProcedurePass {

    override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
        val edges = LinkedHashSet(builder.getEdges())
        for (edge in edges) {
            builder.removeEdge(edge)
            builder.addEdge(edge.withLabel(normalize(edge.label)))
        }
        builder.metaData["normal"] = Unit
        return builder
    }

    private fun normalize(label: XcfaLabel): XcfaLabel {
        val collector: MutableList<MutableList<XcfaLabel>> = ArrayList()
        collector.add(ArrayList())
        normalize(label, collector)
        return NondetLabel(collector.map { SequenceLabel(it) }.toSet())
    }

    private fun normalize(label: XcfaLabel, collector: MutableList<MutableList<XcfaLabel>>) {
        when (label) {
            is SequenceLabel -> label.labels.forEach { normalize(it, collector) }
            is NondetLabel -> {
                val labelList = label.labels.toList()
                ArrayList(collector).forEach { list ->
                    for ((i, xcfaLabel) in labelList.withIndex()) {
                        if (i == labelList.size - 1) {
                            list.add(xcfaLabel)
                        } else {
                            val newList = ArrayList(list)
                            newList.add(xcfaLabel)
                            collector.add(newList)
                        }
                    }
                }
            }

            is NopLabel -> {}
            else -> collector.forEach { it.add(label) }
        }
    }
}