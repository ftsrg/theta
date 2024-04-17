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

import hu.bme.mit.theta.core.model.ImmutableValuation
import hu.bme.mit.theta.core.model.MutableValuation
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.MemoryAssignStmt
import hu.bme.mit.theta.core.stmt.Stmts.Assume
import hu.bme.mit.theta.core.type.abstracttype.NeqExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.False
import hu.bme.mit.theta.core.utils.StmtSimplifier.StmtSimplifierVisitor
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.xcfa.getFlatLabels
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
        val unusedLocRemovalPass = UnusedLocRemovalPass()
        val valuations = LinkedHashMap<XcfaEdge, Valuation>()
        var edges = LinkedHashSet(builder.getEdges())
        lateinit var lastEdges: LinkedHashSet<XcfaEdge>
        do {
            lastEdges = edges

            val toVisit = builder.initLoc.outgoingEdges.toMutableList()
            val visited = mutableSetOf<XcfaEdge>()
            while (toVisit.isNotEmpty()) {
                val edge = toVisit.removeFirst()
                visited.add(edge)

                val incomingValuations = edge.source.incomingEdges
                    .filter { it.getFlatLabels().none { l -> l is StmtLabel && l.stmt == Assume(False()) } }
                    .map(valuations::get).reduceOrNull(this::intersect)
                val localValuation = MutableValuation.copyOf(incomingValuations ?: ImmutableValuation.empty())
                val oldLabels = edge.getFlatLabels()
                val newLabels = oldLabels.map { it.simplify(localValuation) }

                // note that global variable values are still propagated within an edge (XcfaEdge is considered atomic)
                builder.parent.getVars().forEach { localValuation.remove(it.wrappedVar) }

                if (newLabels != oldLabels) {
                    builder.removeEdge(edge)
                    valuations.remove(edge)
                    if (newLabels.firstOrNull().let { (it as? StmtLabel)?.stmt != Assume(False()) }) {
                        val newEdge = edge.withLabel(SequenceLabel(newLabels))
                        builder.addEdge(newEdge)
                        valuations[newEdge] = localValuation
                    }
                } else {
                    valuations[edge] = localValuation
                }

                toVisit.addAll(edge.target.outgoingEdges.filter { it !in visited })
            }
            unusedLocRemovalPass.run(builder)

            edges = LinkedHashSet(builder.getEdges())
        } while (lastEdges != edges)
        builder.metaData["simplifiedExprs"] = Unit
        return builder
    }

    private fun XcfaLabel.simplify(valuation: MutableValuation): XcfaLabel = if (this is StmtLabel) {
        val simplified = stmt.accept(StmtSimplifierVisitor(), valuation).stmt
        when (stmt) {
            is MemoryAssignStmt<*, *> -> {
                simplified as MemoryAssignStmt<*, *>
                if (parseContext.metadata.getMetadataValue(stmt.expr, "cType").isPresent)
                    parseContext.metadata.create(simplified.expr, "cType",
                        CComplexType.getType(stmt.expr, parseContext))
                if (parseContext.metadata.getMetadataValue(stmt.deref, "cType").isPresent)
                    parseContext.metadata.create(simplified.deref, "cType",
                        CComplexType.getType(stmt.deref, parseContext))
                StmtLabel(simplified, metadata = metadata)
            }

            is AssignStmt<*> -> {
                simplified as AssignStmt<*>
                if (parseContext.metadata.getMetadataValue(stmt.expr, "cType").isPresent)
                    parseContext.metadata.create(simplified.expr, "cType",
                        CComplexType.getType(stmt.expr, parseContext))
                StmtLabel(simplified, metadata = metadata)
            }

            is AssumeStmt -> {
                simplified as AssumeStmt
                if (parseContext.metadata.getMetadataValue(stmt.cond, "cType").isPresent) {
                    parseContext.metadata.create(simplified.cond, "cType",
                        CComplexType.getType(stmt.cond, parseContext))
                }
                parseContext.metadata.create(simplified, "cTruth", stmt.cond is NeqExpr<*>)
                StmtLabel(simplified, metadata = metadata, choiceType = choiceType)
            }

            else -> this
        }
    } else this

    private fun intersect(v1: Valuation?, v2: Valuation?): Valuation {
        if (v1 == null || v2 == null) return ImmutableValuation.empty()
        val v1map = v1.toMap()
        val v2map = v2.toMap()
        return ImmutableValuation.from(v1map.filter { v2map.containsKey(it.key) && v2map[it.key] == it.value })
    }
}
