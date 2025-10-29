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

    private fun XcfaBuilder.mallocVar(parseContext: ParseContext) =
      mallocVars.getOrPut(this) { Var("__malloc", CPointer(null, null, parseContext).smtType) }
  }

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
            val ret = invokeLabel.params[0] as RefExpr<*>
            val arg = invokeLabel.params[1]
            if (builder.parent.getVars().none { it.wrappedVar == mallocVar }) { // initial creation
              builder.parent.addVar(
                XcfaGlobalVar(mallocVar, CComplexType.getType(ret, parseContext).nullValue)
              )
              if (MemsafetyPass.enabled) {
                builder.parent.addVar(
                  XcfaGlobalVar(mallocVar, CComplexType.getType(ret, parseContext).nullValue)
                )
              }
              val initProc = builder.parent.getInitProcedures().map { it.first }
              check(initProc.size == 1) { "Multiple start procedure are not handled well" }
              initProc.forEach { proc ->
                val initAssign =
                  StmtLabel(
                    Assign(
                      cast(mallocVar, mallocVar.type),
                      cast(CComplexType.getType(ret, parseContext).nullValue, mallocVar.type),
                    )
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
            val assign1 =
              AssignStmtLabel(
                mallocVar,
                Add(mallocVar.ref, CComplexType.getType(ret, parseContext).getValue("3")),
                ret.type,
                invokeLabel.metadata,
              )
            val assign2 = AssignStmtLabel(ret, cast(mallocVar.ref, ret.type))
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
