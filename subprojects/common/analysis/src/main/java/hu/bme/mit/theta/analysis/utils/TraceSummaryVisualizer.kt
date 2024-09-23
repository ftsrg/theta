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
import hu.bme.mit.theta.analysis.algorithm.tracegeneration.TraceGenerationResult
import hu.bme.mit.theta.common.visualization.Graph

/**
 * This class visualizes not single traces, but a group of traces,
 * connected by trace metadata.
 * The result is an automata-like summary of executions.
 */
sealed class TraceSummaryVisualizer<S: State, A: Action> (
    val stateToString: (S) -> String = { it.toString() },
    val actionToString: (A) -> String = { it.toString() },
    ) {

    // TODO TraceVisualizer has an unused, similar part (visualizeMerged)
    // it does not use metadata, but visualizes a collection of traces
    // (ie, it is not completely the same as TraceSummaryVisualizer::visualize)
    fun visualize(traceGenerationResult : TraceGenerationResult<S, A>,
        traceSummaryId : String = "trace_summary",
        traceSummaryLabel : String = "Trace Summary",
        ) {
        val traces = traceGenerationResult.traces
        val graph : Graph = Graph(traceSummaryId, traceSummaryLabel)


    }
}