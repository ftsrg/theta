/*
 *  Copyright 2023 Budapest University of Technology and Economics
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
import hu.bme.mit.theta.core.stmt.Stmts.Assign
import hu.bme.mit.theta.core.stmt.Stmts.Assume
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.NeqExpr
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.ExprUtils.simplify
import hu.bme.mit.theta.core.utils.StmtUtils
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
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
        val valuation = findConstVariables(builder)
        val edges = LinkedHashSet(builder.getEdges())
        for (edge in edges) {
            val newLabels = (edge.label as SequenceLabel).labels.map {
                if (it is StmtLabel) when (it.stmt) {
                    is AssignStmt<*> -> {
                        val simplified = simplify(it.stmt.expr, valuation)
                        if (parseContext.metadata.getMetadataValue(it.stmt.expr, "cType").isPresent)
                            parseContext.metadata.create(simplified, "cType",
                                CComplexType.getType(it.stmt.expr, parseContext))
                        StmtLabel(Assign(cast(it.stmt.varDecl, it.stmt.varDecl.type),
                            cast(simplified, it.stmt.varDecl.type)), metadata = it.metadata)
                    }

                    is AssumeStmt -> {
                        val simplified = simplify(it.stmt.cond, valuation)
                        if (parseContext.metadata.getMetadataValue(it.stmt.cond, "cType").isPresent) {
                            parseContext.metadata.create(simplified, "cType",
                                CComplexType.getType(it.stmt.cond, parseContext))
                        }
                        parseContext.metadata.create(simplified, "cTruth", it.stmt.cond is NeqExpr<*>)
                        StmtLabel(Assume(simplified), metadata = it.metadata)
                    }

                    else -> it
                } else it
            }
            if (newLabels != edge.label.labels) {
                builder.removeEdge(edge)
                builder.addEdge(edge.withLabel(SequenceLabel(newLabels)))
            }
        }
        builder.metaData["simplifiedExprs"] = Unit
        return builder
    }

    private fun findConstVariables(builder: XcfaProcedureBuilder): Valuation {
        val valuation = MutableValuation()
        builder.parent.getProcedures()
            .flatMap { it.getEdges() }
            .map { it.label.collectVarsWithLabels() }
            .filter { it.isNotEmpty() }.merge()
            .map {
                val writes = it.value.filter { label -> label.isWrite(it.key) }
                if (writes.size == 1 && writes.first() is StmtLabel) {
                    val label = writes.first() as StmtLabel
                    if (label.stmt is AssignStmt<*> && label.stmt.expr.isConst()) {
                        return@map label.stmt
                    }
                }
                null
            }
            .filterNotNull()
            .forEach { assignment ->
                valuation.put(assignment.varDecl, assignment.expr.eval(ImmutableValuation.empty()))
            }
        return valuation
    }

    private fun List<Map<VarDecl<*>, List<XcfaLabel>>>.merge(): Map<VarDecl<*>, List<XcfaLabel>> =
        this.fold(mapOf()) { acc, next ->
            (acc.keys + next.keys).associateWith {
                mutableListOf<XcfaLabel>().apply {
                    acc[it]?.let { addAll(it) }
                    next[it]?.let { addAll(it) }
                }
            }
        }

    private fun XcfaLabel.collectVarsWithLabels(): Map<VarDecl<*>, List<XcfaLabel>> = when (this) {
        is StmtLabel -> StmtUtils.getVars(stmt).associateWith { listOf(this) }
        is NondetLabel -> labels.map { it.collectVarsWithLabels() }.merge()
        is SequenceLabel -> labels.map { it.collectVarsWithLabels() }.merge()
        is InvokeLabel -> params.map { ExprUtils.getVars(it) }.flatten().associateWith { listOf(this) }
        is JoinLabel -> mapOf(pidVar to listOf(this))
        is ReadLabel -> mapOf(global to listOf(this), local to listOf(this))
        is StartLabel -> params.map { ExprUtils.getVars(it) }.flatten()
            .associateWith { listOf(this) } + mapOf(pidVar to listOf(this))

        is WriteLabel -> mapOf(global to listOf(this), local to listOf(this))
        else -> emptyMap()
    }

    private fun XcfaLabel.isWrite(v: VarDecl<*>) =
        this is StmtLabel && this.stmt is AssignStmt<*> && this.stmt.varDecl == v

    private fun <T : Type> Expr<T>.isConst(): Boolean {
        val vars = mutableListOf<VarDecl<*>>()
        ExprUtils.collectVars(this, vars)
        return vars.isEmpty()
    }
}
