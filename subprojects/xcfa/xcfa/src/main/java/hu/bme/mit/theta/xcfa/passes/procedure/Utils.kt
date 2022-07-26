/*
 *  Copyright 2022 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.xcfa.passes.procedure

import hu.bme.mit.theta.xcfa.model.SequenceLabel
import hu.bme.mit.theta.xcfa.model.XcfaEdge
import hu.bme.mit.theta.xcfa.model.XcfaLabel
import hu.bme.mit.theta.xcfa.model.XcfaLocation

fun label2edge(edge: XcfaEdge, label: XcfaLabel) {
    val source = edge.source
    val target = edge.target

}

/**
 * XcfaEdge must be in a `deterministic` ProcedureBuilder
 */
fun XcfaEdge.splitIf(function: (XcfaLabel) -> Boolean): List<XcfaEdge> {
    check(label is SequenceLabel)
    val newLabels = ArrayList<SequenceLabel>()
    var current = ArrayList<XcfaLabel>()
    for (label in label.labels) {
        if(function(label)) {
            if(current.size > 0) {
                newLabels.add(SequenceLabel(current))
                current = ArrayList()
            }
            newLabels.add(SequenceLabel(listOf(label)))
        }
        else {
            current.add(label)
        }
    }
    if(current.size > 0) newLabels.add(SequenceLabel(current))

    val locations = ArrayList<XcfaLocation>()
    locations.add(source)
    for (i in 2..(newLabels.size)) {
        locations.add(XcfaLocation("loc" + XcfaLocation.uniqueCounter()))
    }
    locations.add(target)

    val newEdges = ArrayList<XcfaEdge>()
    for ((i, label) in newLabels.withIndex()) {
        newEdges.add(XcfaEdge(locations[i], locations[i+1], label))
    }
    return newEdges
}
