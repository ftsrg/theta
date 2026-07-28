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

import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.Stmts.Assign
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Add
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CPointer
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.AssignStmtLabel
import hu.bme.mit.theta.xcfa.utils.getFlatLabels

/**
 * Transforms mallocs into address assignments. Requires the ProcedureBuilder be `deterministic`.
 */
class MallocFunctionPass(val parseContext: ParseContext) : ProcedurePass {

  companion object {
    private val mallocVars: MutableMap<XcfaBuilder, VarDecl<*>> = mutableMapOf()

    /**
     * The allocation counter. [AllocaFunctionPass] hands out addresses from the *same* counter, so
     * that a heap block and a stack block can never be given the same base.
     */
    fun XcfaBuilder.mallocVar(parseContext: ParseContext): VarDecl<*> =
      mallocVars.getOrPut(this) { Var("__malloc", CPointer(null, null, parseContext).smtType) }

    /**
     * Creates the shared allocation counter and seeds it to null in the init procedure, once per
     * XCFA. Does nothing if the counter already exists.
     *
     * ⚠️ Must be called *before* a pass starts iterating a snapshot of its own edges. Seeding
     * replaces every outgoing edge of the init procedure's `initLoc` with a new instance carrying
     * the prepended assignment, so any edge captured in a snapshot beforehand is stale. Removing
     * such an edge later dies with "Cannot remove edge if it wasn't already present!" — which is
     * exactly what [AllocaFunctionPass] did on the `*-amalgamation` NN tasks, where `main` allocas
     * and no `malloc` ran first to create the counter.
     */
    fun XcfaBuilder.ensureMallocVar(parseContext: ParseContext, retType: CComplexType) {
      val mallocVar = mallocVar(parseContext)
      if (getVars().any { it.wrappedVar == mallocVar }) return
      addVar(XcfaGlobalVar(mallocVar, retType.nullValue))
      val initProc = getInitProcedures().map { it.first }
      check(initProc.size == 1) { "Multiple start procedure are not handled well" }
      initProc.forEach { proc ->
        val initAssign =
          StmtLabel(Assign(cast(mallocVar, mallocVar.type), cast(retType.nullValue, mallocVar.type)))
        val oldEdges = proc.initLoc.outgoingEdges.toList()
        val newEdges =
          oldEdges.map {
            it.withLabel(
              SequenceLabel(listOf(initAssign) + it.label.getFlatLabels(), it.label.metadata)
            )
          }
        oldEdges.forEach(proc::removeEdge)
        newEdges.forEach(proc::addEdge)
      }
    }

    /**
     * The C type the first allocation call matching [predicate] writes its base into, or null when
     * this procedure performs no such allocation. Lets the counter be seeded before the rewrite
     * loop, without needing an allocation site in hand.
     */
    fun XcfaProcedureBuilder.firstAllocationRetType(
      parseContext: ParseContext,
      predicate: (XcfaLabel) -> Boolean,
    ): CComplexType? =
      getEdges()
        .asSequence()
        .flatMap { it.getFlatLabels().asSequence() }
        .filter(predicate)
        .map { CComplexType.getType((it as InvokeLabel).params[0], parseContext) }
        .firstOrNull()
  }

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    val mallocVar = builder.parent.mallocVar(parseContext)
    checkNotNull(builder.metaData["deterministic"])
    // Seed the counter before the snapshot below is taken: doing it mid-loop invalidates the
    // snapshot's init-procedure edges (see [ensureMallocVar]).
    builder.firstAllocationRetType(parseContext, this::predicate)?.let {
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
          if (predicate((e.label as SequenceLabel).labels[0])) {
            val invokeLabel = e.label.labels[0] as InvokeLabel
            val ret = invokeLabel.params[0] as RefExpr<*>
            val arg = invokeLabel.params[1]
            val assign1 =
              AssignStmtLabel(
                mallocVar,
                Add(mallocVar.ref, CComplexType.getType(ret, parseContext).getValue("3")),
                ret.type,
                EmptyMetaData,
              )
            val assign2 =
              AssignStmtLabel(
                ret,
                cast(
                  FlatMemoryPass.flatBaseExpr(
                    mallocVar.ref,
                    CComplexType.getType(ret, parseContext),
                    parseContext,
                  ),
                  ret.type,
                ),
              )
            val labels =
              if (MemsafetyPass.enabled) {
                val assign3 = builder.parent.allocate(parseContext, ret, arg)
                listOf(assign1, assign2, assign3)
              } else {
                listOf(assign1, assign2)
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
    return it is InvokeLabel && it.name == "malloc"
  }
}
