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

import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Add
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.AssignStmtLabel
import hu.bme.mit.theta.xcfa.utils.POINTER_BASE_CLASSES
import hu.bme.mit.theta.xcfa.utils.bumpAllocate
import hu.bme.mit.theta.xcfa.utils.ensureMallocVar
import hu.bme.mit.theta.xcfa.utils.firstAllocationRetType
import hu.bme.mit.theta.xcfa.utils.mallocCells
import hu.bme.mit.theta.xcfa.utils.mallocVar

/**
 * Transforms `malloc` into an address assignment out of the shared allocation counter, in the heap
 * residue class (see `POINTER_BASE_CLASSES`).
 *
 * Under flat addressing a block is instead the next slot of the address line, sized by the request
 * (see `bumpAllocate`).
 *
 * `realloc` is handled here too, as an **in-place resize**: the returned pointer keeps the old base
 * and the object's size becomes the new one. A program must use realloc's return value whether or
 * not the block moved, so returning the same base preserves the observable contents exactly and
 * still gives the new bound to the memsafety size domain. What it does not model is the
 * invalidation of the old pointer, the same imprecision the analysis already has around frees;
 * `realloc(NULL, n)` and `realloc(q, 0)` are likewise left as the in-place resize. Under flat
 * addressing a block grown past its slot overlaps the blocks allocated after it.
 *
 * Requires the ProcedureBuilder be `deterministic`.
 */
class MallocFunctionPass(val parseContext: ParseContext) : ProcedurePass {

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    val mallocVar = builder.parent.mallocVar(parseContext)
    checkNotNull(builder.metaData["deterministic"])
    // Seed the counter before the snapshot below is taken: doing it mid-loop invalidates the
    // snapshot's init-procedure edges (see ensureMallocVar).
    builder.firstAllocationRetType(parseContext, this::isMalloc)?.let {
      builder.parent.ensureMallocVar(parseContext, it)
    }
    for (edge in ArrayList(builder.getEdges())) {
      val edges = edge.splitIf(this::predicate)
      if (
        edges.size > 1 ||
          (edges.size == 1 && predicate((edges[0].label as SequenceLabel).labels[0]))
      ) {
        builder.removeEdge(edge)
        edges.forEach { e ->
          val head = (e.label as SequenceLabel).labels[0]
          if (!predicate(head)) {
            builder.addEdge(e)
            return@forEach
          }
          val invokeLabel = head as InvokeLabel
          val labels =
            if (isMalloc(invokeLabel)) allocate(builder, invokeLabel, mallocVar)
            else reallocate(builder, invokeLabel)
          builder.addEdge(XcfaEdge(e.source, e.target, SequenceLabel(labels), e.metadata))
        }
      }
    }
    return builder
  }

  private fun allocate(
    builder: XcfaProcedureBuilder,
    invokeLabel: InvokeLabel,
    mallocVar: VarDecl<*>,
  ): List<XcfaLabel> {
    val ret = invokeLabel.params[0] as RefExpr<*>
    val arg = invokeLabel.params[1]
    val sizeLabels =
      if (MemsafetyPass.enabled)
        listOf(builder.parent.allocate(parseContext, ret, bound(builder, ret, arg)))
      else listOf()
    if (parseContext.memoryModel.flatAddressing()) {
      return builder.parent.bumpAllocate(parseContext, ret, arg, heap = true) + sizeLabels
    }
    val bump =
      AssignStmtLabel(
        mallocVar,
        Add(
          mallocVar.ref,
          CComplexType.getType(ret, parseContext).getValue("$POINTER_BASE_CLASSES"),
        ),
        ret.type,
        EmptyMetaData,
      )
    val assignRet = AssignStmtLabel(ret, cast(mallocVar.ref, ret.type))
    return listOf(bump, assignRet) + sizeLabels
  }

  private fun reallocate(builder: XcfaProcedureBuilder, invokeLabel: InvokeLabel): List<XcfaLabel> {
    val ret = invokeLabel.params[0] as RefExpr<*>
    val oldPtr = invokeLabel.params[1]
    val newSize = invokeLabel.params[2]
    val keepBase = AssignStmtLabel(ret, cast(oldPtr, ret.type))
    return if (MemsafetyPass.enabled) {
      listOf(keepBase, builder.parent.allocate(parseContext, ret, bound(builder, ret, newSize)))
    } else {
      listOf(keepBase)
    }
  }

  /** The size recorded for memsafety: cells under flat addressing where known, else bytes. */
  private fun bound(builder: XcfaProcedureBuilder, ret: Expr<*>, bytes: Expr<*>): Expr<*> =
    if (parseContext.memoryModel.flatAddressing() && !parseContext.memoryModel.byteAddressed())
      builder.mallocCells(parseContext, ret, bytes) ?: bytes
    else bytes

  private fun isMalloc(it: XcfaLabel): Boolean = it is InvokeLabel && it.name == "malloc"

  private fun predicate(it: XcfaLabel): Boolean =
    it is InvokeLabel && (it.name == "malloc" || it.name == "realloc")
}
