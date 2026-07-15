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

import hu.bme.mit.theta.core.stmt.Stmts.Assign
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Add
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.passes.MallocFunctionPass.Companion.mallocVar
import hu.bme.mit.theta.xcfa.utils.AssignStmtLabel
import hu.bme.mit.theta.xcfa.utils.getFlatLabels

/**
 * Turns `alloca(size)` into an address assignment, like [MallocFunctionPass] does for `malloc`, but
 * places the block in a different residue class of the pointer base space.
 *
 * The target `alloca(target, size)` writes the fresh base into may be a variable (a plain `alloca`,
 * or a stack-allocated struct/array whose value is its base) or a memory cell (a struct's
 * struct/array-typed *field*, whose base lives at `arrays[parent][i]`). The assignment dispatches on
 * which -- an ordinary assign for the variable, a memory-write for the cell -- so that every stack
 * object gets a *fresh runtime* base per allocation. A compile-time constant base would be the same
 * for every activation of the procedure, so two recursive frames or two threads running it would
 * alias; a runtime base from the shared counter cannot.
 *
 * Pointer bases are partitioned by residue mod 3: `3k+0` is malloc'd heap memory, `3k+2` is
 * address-taken locals ([ReferenceElimination]). The memcleanup check
 * ([MemsafetyPass.annotateLost]) scans `3k+0` only, so a block that is *not* the program's
 * responsibility to free must not live there. Memory from `alloca` is released automatically when
 * the enclosing function returns, so reporting it as a leak would be wrong; it therefore gets the
 * free residue class, `3k+1`. It still records a real size in `__theta_ptr_size`, so out-of-bounds
 * accesses to it are caught exactly as they are for heap memory.
 *
 * The shared `__malloc` counter is bumped by 3 for every allocation of either kind, so each
 * allocation consumes its own `k` and no two blocks can alias.
 *
 * Known gaps (both are the pre-existing scope-lifetime limitation, not new to alloca): the block is
 * never invalidated at function return, so a dangling access to it afterwards is not caught, and
 * `free()`ing it is accepted rather than reported as an invalid free.
 *
 * Requires the ProcedureBuilder be `deterministic`.
 */
class AllocaFunctionPass(val parseContext: ParseContext) : ProcedurePass {

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    val mallocVar = builder.parent.mallocVar(parseContext)
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
            // The target may be a variable (a bare `alloca`, or a stack struct/array) or a memory
            // cell (a struct/array-typed field). AssignStmtLabel below dispatches on which.
            val ret = invokeLabel.params[0]
            val arg = invokeLabel.params[1]
            val retType = CComplexType.getType(ret, parseContext)
            if (builder.parent.getVars().none { it.wrappedVar == mallocVar }) { // initial creation
              builder.parent.addVar(XcfaGlobalVar(mallocVar, retType.nullValue))
              val initProc = builder.parent.getInitProcedures().map { it.first }
              check(initProc.size == 1) { "Multiple start procedure are not handled well" }
              initProc.forEach { proc ->
                val initAssign =
                  StmtLabel(
                    Assign(cast(mallocVar, mallocVar.type), cast(retType.nullValue, mallocVar.type))
                  )
                val newEdges =
                  proc.initLoc.outgoingEdges.map {
                    it.withLabel(
                      SequenceLabel(
                        listOf(initAssign) + it.label.getFlatLabels(),
                        it.label.metadata,
                      )
                    )
                  }
                proc.initLoc.outgoingEdges.forEach(proc::removeEdge)
                newEdges.forEach(proc::addEdge)
              }
            }
            val bump =
              AssignStmtLabel(
                mallocVar,
                Add(mallocVar.ref, retType.getValue("3")),
                ret.type,
                EmptyMetaData,
              )
            // 3k+1: the residue class the memcleanup scan does not enumerate.
            val assignRet =
              AssignStmtLabel(ret, cast(Add(mallocVar.ref, retType.getValue("1")), ret.type))
            val labels =
              if (MemsafetyPass.enabled) {
                listOf(bump, assignRet, builder.parent.allocate(parseContext, ret, arg))
              } else {
                listOf(bump, assignRet)
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
    return it is InvokeLabel && it.name == "alloca"
  }
}
