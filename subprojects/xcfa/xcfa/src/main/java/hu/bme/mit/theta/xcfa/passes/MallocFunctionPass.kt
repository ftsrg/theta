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

package hu.bme.mit.theta.xcfa.passes

import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.Stmts.Assign
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Add
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CPointer
import hu.bme.mit.theta.xcfa.getFlatLabels
import hu.bme.mit.theta.xcfa.model.*
import org.abego.treelayout.internal.util.Contract.checkState

/**
 * Transforms mallocs into address assignments.
 * Requires the ProcedureBuilder be `deterministic`.
 */
class MallocFunctionPass(val parseContext: ParseContext) : ProcedurePass {

    private val XcfaBuilder.malloc: VarDecl<*> by lazy {
        Var("__malloc", CPointer(null, null, parseContext).smtType)
    }

    override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
        checkNotNull(builder.metaData["deterministic"])
        for (edge in ArrayList(builder.getEdges())) {
            val edges = edge.splitIf(this::predicate)
            if (edges.size > 1 || (edges.size == 1 && predicate(
                    (edges[0].label as SequenceLabel).labels[0]))) {
                builder.removeEdge(edge)
                edges.forEach {
                    if (predicate((it.label as SequenceLabel).labels[0])) {
                        val invokeLabel = it.label.labels[0] as InvokeLabel
                        val ret = invokeLabel.params[0] as RefExpr<*>
                        val mallocVar = builder.parent.malloc
                        if (builder.parent.getVars().none { it.wrappedVar == mallocVar }) { // initial creation
                            builder.parent.addVar(
                                XcfaGlobalVar(mallocVar, CComplexType.getType(ret, parseContext).nullValue))
                            val initProc = builder.parent.getInitProcedures().map { it.first }
                            checkState(initProc.size == 1, "Multiple start procedure are not handled well")
                            initProc.forEach {
                                val initAssign = StmtLabel(Assign(cast(mallocVar, mallocVar.type),
                                    cast(CComplexType.getType(ret, parseContext).nullValue, mallocVar.type)))
                                val newEdges = it.initLoc.outgoingEdges.map {
                                    it.withLabel(
                                        SequenceLabel(listOf(initAssign) + it.label.getFlatLabels(), it.label.metadata))
                                }
                                it.initLoc.outgoingEdges.forEach(it::removeEdge)
                                newEdges.forEach(it::addEdge)
                            }
                        }
                        val assign1 = AssignStmt.of(
                            cast(mallocVar, ret.type),
                            cast(Add(mallocVar.ref, CComplexType.getType(ret, parseContext).getValue("3")),
                                ret.type))
                        val assign2 = AssignStmt.of(
                            cast(ret.decl as VarDecl<*>, ret.type), cast(mallocVar.ref, ret.type))
                        builder.addEdge(XcfaEdge(it.source, it.target, SequenceLabel(
                            listOf(
                                StmtLabel(assign1, metadata = invokeLabel.metadata),
                                StmtLabel(assign2, metadata = invokeLabel.metadata)))))
                    } else {
                        builder.addEdge(it)
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