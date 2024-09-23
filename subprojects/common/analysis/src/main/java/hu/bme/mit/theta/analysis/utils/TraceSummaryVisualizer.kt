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

package hu.bme.mit.theta.analysis.utils

import hu.bme.mit.theta.analysis.Action
import hu.bme.mit.theta.analysis.State
import hu.bme.mit.theta.analysis.algorithm.tracegeneration.TraceSetSummary
import hu.bme.mit.theta.common.visualization.EdgeAttributes
import hu.bme.mit.theta.common.visualization.Graph
import hu.bme.mit.theta.common.visualization.LineStyle
import hu.bme.mit.theta.common.visualization.NodeAttributes
import java.awt.Color

/**
 * This class visualizes not single traces, but a group of traces,
 * connected by trace metadata.
 * The result is an automata-like summary of executions.
 */
object TraceSummaryVisualizer {
    val lineStyle: LineStyle = LineStyle.NORMAL
    val fillColor: Color = Color.WHITE
    val lineColor: Color = Color.BLACK

    // TODO TraceVisualizer has an unused, similar part (visualizeMerged)
    // it does not use metadata, but visualizes a collection of traces
    // (ie, it is not completely the same as TraceSummaryVisualizer::visualize)
    fun <S: State, A: Action> visualize(
        traceSetSummary: TraceSetSummary<S, A>,
        traceSummaryId: String = "trace_summary",
        traceSummaryLabel: String = "Trace Summary",
    ) : Graph {
        val graph : Graph = Graph(traceSummaryId, traceSummaryLabel)

        // add nodes
        val stateNodeSummaries = traceSetSummary.summaryNodes
        for(stateNodeSummary in stateNodeSummaries) {
            val nAttribute = NodeAttributes.builder()
                .label(stateNodeSummary.getLabel())
                .fillColor(fillColor).lineColor(lineColor)
                .lineStyle(lineStyle).build()

            graph.addNode(stateNodeSummary.nodeSummaryId.toString(), nAttribute)
        }

        for(summaryEdge in traceSetSummary.summaryEdges) {
            val eAttribute = EdgeAttributes.builder()
                .label(summaryEdge.getLabel())
                .color(lineColor)
                .lineStyle(lineStyle).build()

            graph.addEdge(
                summaryEdge.source.nodeSummaryId.toString(),
                summaryEdge.target.nodeSummaryId.toString(),
                eAttribute
            )
        }

        return graph
    }
}