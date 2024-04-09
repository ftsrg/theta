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

import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.ImmutableValuation
import hu.bme.mit.theta.core.model.MutableValuation
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.MemoryAssignStmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.NeqExpr
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.StmtSimplifier.StmtSimplifierVisitor
import hu.bme.mit.theta.core.utils.StmtUtils
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.xcfa.collectVarsWithAccessType
import hu.bme.mit.theta.xcfa.isRead
import hu.bme.mit.theta.xcfa.model.*

/**
 * This pass simplifies the expressions inside statements and substitutes the values of constant variables
 * (that is, variables assigned only once).
 * Requires the ProcedureBuilder to be `deterministic` (@see DeterministicPass)
 * Sets the `simplifiedExprs` flag on the ProcedureBuilder
 */

class SimplifyExprsPass(val parseContext: ParseContext) : ProcedurePass {

    override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
        checkNotNull(builder.metaData["deterministic"])
        removeUnusedGlobalVarWrites(builder)
        val valuations = LinkedHashMap<XcfaEdge, Valuation>()
        var edges = LinkedHashSet(builder.getEdges())
        lateinit var lastEdges: LinkedHashSet<XcfaEdge>
        do {
            lastEdges = edges
            for (edge in edges) {
                val incomingValuations = edge.source.incomingEdges.map(valuations::get)
                    .reduceOrNull(this::intersect)
                val localValuation = MutableValuation.copyOf(incomingValuations ?: ImmutableValuation.empty())
                val newLabels = (edge.label as SequenceLabel).labels.map {
                    if (it is StmtLabel) {
                        val simplified = it.stmt.accept(StmtSimplifierVisitor(), localValuation).stmt
                        when (it.stmt) {
                            is MemoryAssignStmt<*, *> -> {
                                simplified as MemoryAssignStmt<*, *>
                                if (parseContext.metadata.getMetadataValue(it.stmt.expr, "cType").isPresent)
                                    parseContext.metadata.create(simplified.expr, "cType",
                                        CComplexType.getType(it.stmt.expr, parseContext))
                                if (parseContext.metadata.getMetadataValue(it.stmt.deref, "cType").isPresent)
                                    parseContext.metadata.create(simplified.deref, "cType",
                                        CComplexType.getType(it.stmt.deref, parseContext))
                                StmtLabel(simplified, metadata = it.metadata)
                            }

                            is AssignStmt<*> -> {
                                simplified as AssignStmt<*>
                                if (parseContext.metadata.getMetadataValue(it.stmt.expr, "cType").isPresent)
                                    parseContext.metadata.create(simplified.expr, "cType",
                                        CComplexType.getType(it.stmt.expr, parseContext))
                                StmtLabel(simplified, metadata = it.metadata)
                            }

                            is AssumeStmt -> {
                                simplified as AssumeStmt
                                if (parseContext.metadata.getMetadataValue(it.stmt.cond, "cType").isPresent) {
                                    parseContext.metadata.create(simplified.cond, "cType",
                                        CComplexType.getType(it.stmt.cond, parseContext))
                                }
                                parseContext.metadata.create(simplified, "cTruth", it.stmt.cond is NeqExpr<*>)
                                StmtLabel(simplified, metadata = it.metadata, choiceType = it.choiceType)
                            }

                            else -> it
                        }
                    } else it
                }
                if (newLabels != edge.label.labels) {
                    builder.removeEdge(edge)
                    val newEdge = edge.withLabel(SequenceLabel(newLabels))
                    builder.addEdge(newEdge)
                    valuations[newEdge] = localValuation
                    valuations.remove(edge)
                } else {
                    valuations[edge] = localValuation
                }
            }
            edges = LinkedHashSet(builder.getEdges())
        } while (lastEdges != edges)
        builder.metaData["simplifiedExprs"] = Unit
        return builder
    }

    private fun removeUnusedGlobalVarWrites(builder: XcfaProcedureBuilder) {
        val usedVars = mutableSetOf<VarDecl<*>>()
        val xcfaBuilder = builder.parent
        xcfaBuilder.getProcedures().flatMap { it.getEdges() }.forEach {
            it.label.collectVarsWithAccessType().forEach { (varDecl, access) ->
                if (access.isRead) usedVars.add(varDecl)
            }
        }
        val unusedVars = xcfaBuilder.getVars().map { it.wrappedVar } union builder.getVars() subtract
            usedVars subtract builder.getParams().map { it.first }.toSet()
        xcfaBuilder.getProcedures().forEach { b ->
            b.getEdges().toList().forEach { edge ->
                val newLabel = edge.label.removeUnusedWrites(unusedVars)
                b.removeEdge(edge)
                b.addEdge(edge.withLabel(newLabel))
            }
        }
    }

    private fun intersect(v1: Valuation?, v2: Valuation?): Valuation {
        if (v1 == null || v2 == null) return ImmutableValuation.empty()
        val v1map = v1.toMap()
        val v2map = v2.toMap()
        return ImmutableValuation.from(v1map.filter { v2map.containsKey(it.key) && v2map[it.key] == it.value })
    }
}
