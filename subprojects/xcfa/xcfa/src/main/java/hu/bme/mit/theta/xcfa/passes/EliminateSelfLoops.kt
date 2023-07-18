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
import hu.bme.mit.theta.xcfa.model.NopLabel
import hu.bme.mit.theta.xcfa.model.XcfaEdge
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import hu.bme.mit.theta.xcfa.model.XcfaProcedureBuilder
import java.util.stream.Collectors

class EliminateSelfLoops(val parseContext: ParseContext) : ProcedurePass {

    override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
        val selfLoops: Set<XcfaEdge> = builder.getEdges().stream()
            .filter { xcfaEdge -> xcfaEdge.source === xcfaEdge.target }.collect(Collectors.toSet())
        for (selfLoop in selfLoops) {
            builder.removeEdge(selfLoop)
            val source = selfLoop.source
            val target: XcfaLocation = XcfaLocation(
                source.name + "_" + XcfaLocation.uniqueCounter())
            builder.addLoc(target)
            for (outgoingEdge in LinkedHashSet(source.outgoingEdges)) {
                builder.removeEdge(outgoingEdge)
                builder.addEdge(XcfaEdge(target, outgoingEdge.target, outgoingEdge.label))
            }
            builder.addEdge(XcfaEdge(source, target, selfLoop.label))
            builder.addEdge(XcfaEdge(target, source, NopLabel))
        }
        builder.metaData["noSelfLoops"] = Unit
        return builder
    }
}