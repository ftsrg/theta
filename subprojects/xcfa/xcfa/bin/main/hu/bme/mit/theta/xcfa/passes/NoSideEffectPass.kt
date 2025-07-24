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

import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.xcfa.model.*

/**
 * Transforms all ignored calls into nop/skip labels. Requires the ProcedureBuilder be
 * `deterministic`.
 */
class NoSideEffectPass(val parseContext: ParseContext) : ProcedurePass {

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    checkNotNull(builder.metaData["deterministic"])
    for (edge in ArrayList(builder.getEdges())) {
      val edges = edge.splitIf(this::predicate)
      if (
        edges.size > 1 ||
          (edges.size == 1 && predicate((edges[0].label as SequenceLabel).labels[0]))
      ) {
        builder.removeEdge(edge)
        edges.forEach {
          if (predicate((it.label as SequenceLabel).labels[0])) {
            builder.addEdge(
              XcfaEdge(it.source, it.target, SequenceLabel(listOf(NopLabel)), it.metadata)
            )
          } else {
            builder.addEdge(it)
          }
        }
      }
    }
    return builder
  }

  private fun predicate(label: XcfaLabel): Boolean {
    return label is InvokeLabel &&
      listOf(
          Regex("sleep"),
          Regex("free"),
          Regex("pthread_mutex_destroy"), // TODO: is this safe?
        )
        .any { label.name.matches(it) }
  }
}
