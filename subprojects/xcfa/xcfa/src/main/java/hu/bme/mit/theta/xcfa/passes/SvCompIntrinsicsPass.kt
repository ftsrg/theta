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
import kotlin.jvm.optionals.getOrNull

/**
 * Transforms the following SV-COMP intrinsics into model elements:
 *      - __VERIFIER_atomic_begin()
 *      - __VERIFIER_atomic_end()
 *      - __VERIFIER_atomic_*
 * Requires the ProcedureBuilder be `deterministic`.
 */
@OptIn(ExperimentalStdlibApi::class)
class SvCompIntrinsicsPass(val parseContext: ParseContext) : ProcedurePass {

    override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
        checkNotNull(builder.metaData["deterministic"])
        if (builder.name.startsWith("__VERIFIER_atomic")) {
            for (outgoingEdge in ArrayList(builder.initLoc.outgoingEdges)) {
                builder.removeEdge(outgoingEdge)
                val labels: MutableList<XcfaLabel> = ArrayList()
                labels.add(FenceLabel(setOf("ATOMIC_BEGIN"), metadata = outgoingEdge.metadata))
                labels.addAll((outgoingEdge.label as SequenceLabel).labels)
                builder.addEdge(outgoingEdge.withLabel(SequenceLabel(labels)))
            }
            for (incomingEdge in ArrayList(
                builder.finalLoc.getOrNull()?.incomingEdges ?: listOf())) {
                builder.removeEdge(incomingEdge)
                val labels = ArrayList((incomingEdge.label as SequenceLabel).labels)
                labels.add(FenceLabel(setOf("ATOMIC_END"), metadata = incomingEdge.metadata))
                builder.addEdge(incomingEdge.withLabel(SequenceLabel(labels)))
            }
        }
        for (edge in ArrayList(builder.getEdges())) {
            val edges = edge.splitIf(this::predicate)
            if (edges.size > 1 || (edges.size == 1 && predicate(
                    (edges[0].label as SequenceLabel).labels[0]))) {
                builder.removeEdge(edge)
                val labels: MutableList<XcfaLabel> = ArrayList()
                edges.forEach {
                    if (predicate((it.label as SequenceLabel).labels[0])) {
                        val invokeLabel = it.label.labels[0] as InvokeLabel
                        val fence = when (invokeLabel.name) {
                            "__VERIFIER_atomic_begin" -> FenceLabel(setOf("ATOMIC_BEGIN"),
                                metadata = invokeLabel.metadata)

                            "__VERIFIER_atomic_end" -> FenceLabel(setOf("ATOMIC_END"),
                                metadata = invokeLabel.metadata)

                            else -> invokeLabel
                        }
                        labels.add(fence)
                    } else {
                        labels.addAll(it.label.labels)
                    }
                }
                builder.addEdge(edge.withLabel(SequenceLabel(labels)))
            }
        }
        return builder
    }

    private fun predicate(it: XcfaLabel): Boolean {
        return it is InvokeLabel && it.name.startsWith("__VERIFIER_atomic")
    }
}