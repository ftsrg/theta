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

import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.core.stmt.Stmts.Skip
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.xcfa.model.*

/**
 * Replaces every remaining call to an unresolved function (one that is neither a procedure defined
 * in the XCFA nor handled by an earlier pass such as [CLibraryFunctionsPass], [MallocFunctionPass]
 * or [NondetFunctionPass]) with a havoc of its return value.
 *
 * This must run after [InlineProceduresPass]/[NondetFunctionPass], so that genuine (including
 * recursive) procedures and modeled library functions are already gone. Without it, such calls
 * survive into the analysis and crash it later with "No such method ...".
 *
 * The return value (the synthetic `params[0]` slot the frontend prepends to every call) is havoced,
 * modeling a nondeterministic return. Any side effects the callee may have through pointer
 * arguments or globals are NOT modeled, so a warning is emitted.
 */
class UnresolvedInvokeToHavocPass(private val uniqueWarningLogger: Logger) : ProcedurePass {

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    val definedProcedures = builder.parent.getProcedures().map { it.name }.toSet()
    val pred: (XcfaLabel) -> Boolean = { it is InvokeLabel && it.name !in definedProcedures }

    for (edge in ArrayList(builder.getEdges())) {
      val edges = edge.splitIf(pred)
      if (
        edges.size > 1 || (edges.size == 1 && pred((edges[0].label as SequenceLabel).labels[0]))
      ) {
        builder.removeEdge(edge)
        edges.forEach {
          if (pred((it.label as SequenceLabel).labels[0])) {
            val invokeLabel = it.label.labels[0] as InvokeLabel
            uniqueWarningLogger.write(
              Logger.Level.INFO,
              "WARNING: call to unresolved function %s is modeled as a havoc of its return value;" +
                " any side effects (e.g. writes through pointer arguments or to globals) are" +
                " swallowed.\n",
              invokeLabel.name,
            )
            val returnSlot = invokeLabel.params.getOrNull(0)
            val replacement =
              if (returnSlot is RefExpr<*> && returnSlot.decl is VarDecl<*>) {
                HavocStmt.of(returnSlot.decl as VarDecl<*>)
              } else {
                Skip()
              }
            builder.addEdge(
              XcfaEdge(
                it.source,
                it.target,
                SequenceLabel(listOf(StmtLabel(replacement, metadata = invokeLabel.metadata))),
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
}
