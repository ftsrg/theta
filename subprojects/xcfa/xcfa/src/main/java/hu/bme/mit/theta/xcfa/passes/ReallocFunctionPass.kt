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

import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.AssignStmtLabel

/**
 * Models `p = realloc(q, n)` as an **in-place resize**: the returned pointer keeps `q`'s base, and
 * the object's size becomes `n`. Requires the ProcedureBuilder be `deterministic`; runs after
 * [MallocFunctionPass] so an unmodeled `realloc` no longer reaches the analysis as a live call and
 * crashes it ("No such method realloc").
 *
 * A program must use realloc's *return value* whether or not the block physically moved, so
 * returning the same base preserves exactly the observable contents and gives the new bound to the
 * memsafety size domain -- no havoc (which would false-alarm on the copied data), no crash. What it
 * does not model is the invalidation of the *old* pointer: a use-after-realloc of `q` looks valid
 * here, the same imprecision the analysis already has around frees. The `realloc(NULL, n)` (==
 * malloc) and `realloc(q, 0)` (== free) corner cases are likewise left as the in-place resize.
 */
class ReallocFunctionPass(val parseContext: ParseContext) : ProcedurePass {

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    checkNotNull(builder.metaData["deterministic"])
    for (edge in ArrayList(builder.getEdges())) {
      val edges = edge.splitIf(this::predicate)
      if (
        edges.size > 1 ||
          (edges.size == 1 && predicate((edges[0].label as SequenceLabel).labels[0]))
      ) {
        builder.removeEdge(edge)
        edges.forEach { e ->
          if (predicate((e.label as SequenceLabel).labels[0])) {
            val invokeLabel = e.label.labels[0] as InvokeLabel
            val ret = invokeLabel.params[0] as RefExpr<*>
            val oldPtr = invokeLabel.params[1]
            val newSize = invokeLabel.params[2]
            val keepBase = AssignStmtLabel(ret, cast(oldPtr, ret.type))
            val labels =
              if (MemsafetyPass.enabled) {
                listOf(keepBase, builder.parent.allocate(parseContext, ret, newSize))
              } else {
                listOf(keepBase)
              }
            builder.addEdge(XcfaEdge(e.source, e.target, SequenceLabel(labels), e.metadata))
          } else {
            builder.addEdge(e)
          }
        }
      }
    }
    return builder
  }

  private fun predicate(it: XcfaLabel): Boolean {
    return it is InvokeLabel && it.name == "realloc"
  }
}
