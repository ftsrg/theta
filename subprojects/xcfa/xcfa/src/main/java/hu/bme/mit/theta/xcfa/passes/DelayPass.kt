/*
 *  Copyright 2025 Budapest University of Technology and Economics
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
import hu.bme.mit.theta.xcfa.model.ClockDelayLabel
import hu.bme.mit.theta.xcfa.model.ClockOpLabel
import hu.bme.mit.theta.xcfa.model.SequenceLabel
import hu.bme.mit.theta.xcfa.model.XcfaProcedureBuilder
import java.util.ArrayList

class DelayPass(val timed : Boolean) : ProcedurePass {

    override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
        if (timed) {
            for (edge in ArrayList(builder.getEdges())) {
                if (edge.getFlatLabels().any { it is ClockOpLabel }) {
                    builder.removeEdge(edge)

                    val newLabels = ArrayList((edge.label as SequenceLabel).labels)
                    newLabels.add(0, ClockDelayLabel())

                    builder.addEdge(edge.withLabel(SequenceLabel(newLabels)))
                }
            }
        }
        return builder
    }
}
