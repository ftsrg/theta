/*
 *  Copyright 2026 Budapest University of Technology and Economics
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
 * Inlines all procedure invocations in the current procedure. Requires the ProcedureBuilder to be
 * `deterministic`. Sets the `inlined` flag on the ProcedureBuilder if successful.
 */
class InlineProceduresPass(val parseContext: ParseContext) : ProcedurePass {

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    if (!builder.canInline()) return builder
    checkNotNull(builder.metaData["deterministic"])
    check(builder.metaData["inlined"] == null) {
      "Recursive programs are not supported by inlining."
    }
    builder.metaData["inlined"] = Unit
    while (true) {
      var foundOne = false
      for (edge in ArrayList(builder.getEdges())) {
        val pred: (XcfaLabel) -> Boolean = { builder.callsKnownProcedure(it) }
        val edges = edge.splitIf(pred)
        if (
          edges.size > 1 || (edges.size == 1 && pred((edges[0].label as SequenceLabel).labels[0]))
        ) {
          builder.removeEdge(edge)
          edges.forEach { e ->
            if (pred((e.label as SequenceLabel).labels[0])) {
              foundOne = true
              val invokeLabel: InvokeLabel = e.label.labels[0] as InvokeLabel
              val procedure = checkNotNull(builder.calleeOf(invokeLabel))
              val inlineIndex =
                builder.manager.passes.indexOfFirst { phase ->
                  phase.any { pass -> pass is InlineProceduresPass }
                }
              procedure.optimize(inlineIndex)
              inlineCallSite(
                builder = builder,
                source = e.source,
                target = e.target,
                invokeLabel = invokeLabel,
                callee = procedure.snapshotBody(),
                parseContext = parseContext,
                metadata = e.metadata,
              )
            } else {
              builder.addEdge(e)
            }
          }
        }
      }
      if (!foundOne) {
        return builder
      }
    }
  }
}
