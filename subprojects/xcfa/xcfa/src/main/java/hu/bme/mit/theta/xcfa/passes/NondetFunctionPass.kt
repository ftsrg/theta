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
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.xcfa.model.*

/**
 * Transforms calls to the `__VERIFIER_nondet*` intrinsics into havocs. Requires the
 * ProcedureBuilder be `deterministic`.
 *
 * Only calls that do NOT resolve to a procedure defined in the XCFA are havoced: a program may
 * define its own function whose name happens to start with `__VERIFIER_nondet` (SV-COMP's
 * memory-model benchmarks do), and havocing such a call would silently discard its body -- an
 * under-approximation that can prove an unsafe program safe.
 */
class NondetFunctionPass(val parseContext: ParseContext) : ProcedurePass {

  private var definedProcedures: Set<String> = emptySet()

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    checkNotNull(builder.metaData["deterministic"])
    definedProcedures = builder.parent.getProcedures().map { it.name }.toSet()
    for (edge in ArrayList(builder.getEdges())) {
      val edges = edge.splitIf(this::predicate)
      if (
        edges.size > 1 ||
          (edges.size == 1 && predicate((edges[0].label as SequenceLabel).labels[0]))
      ) {
        builder.removeEdge(edge)
        edges.forEach {
          if (predicate((it.label as SequenceLabel).labels[0])) {
            val invokeLabel = it.label.labels[0] as InvokeLabel
            check(invokeLabel.params.size == 1) {
              "Nondet function ${invokeLabel.name} with arguments is not supported: " +
                "havocing the return value would silently drop the effect on the arguments."
            }
            val slot = invokeLabel.params[0] as RefExpr<*>
            val havoc = HavocStmt.of(slot.decl as VarDecl<*>)
            builder.addEdge(
              XcfaEdge(
                it.source,
                it.target,
                SequenceLabel(
                  listOf(StmtLabel(havoc, metadata = invokeLabel.metadata)) +
                    withinTypeRange(slot, parseContext, invokeLabel.metadata)
                ),
                it.metadata,
              )
            )
          } else {
            builder.addEdge(it)
          }
        }
      }
    }
    return builder
  }

  private fun predicate(it: XcfaLabel): Boolean {
    return it is InvokeLabel &&
      it.name.startsWith("__VERIFIER_nondet") &&
      it.name !in definedProcedures
  }
}
