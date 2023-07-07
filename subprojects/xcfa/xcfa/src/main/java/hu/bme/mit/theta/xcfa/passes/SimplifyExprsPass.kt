/*
 *  Copyright 2022 Budapest University of Technology and Economics
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

import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.Stmts.Assign
import hu.bme.mit.theta.core.stmt.Stmts.Assume
import hu.bme.mit.theta.core.type.abstracttype.NeqExpr
import hu.bme.mit.theta.core.utils.ExprUtils.simplify
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.frontend.FrontendMetadata
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.xcfa.model.SequenceLabel
import hu.bme.mit.theta.xcfa.model.StmtLabel
import hu.bme.mit.theta.xcfa.model.XcfaProcedureBuilder

/**
 * This pass simplifies the expressions inside statements.
 * Requires the ProcedureBuilder to be `deterministic` (@see DeterministicPass)
 * Sets the `simplifiedExprs` flag on the ProcedureBuilder
 */

class SimplifyExprsPass : ProcedurePass {
    override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
        checkNotNull(builder.metaData["deterministic"])
        val edges = LinkedHashSet(builder.getEdges())
        for (edge in edges) {
            val newLabels = (edge.label as SequenceLabel).labels.map { if(it is StmtLabel) when(it.stmt) {
                is AssignStmt<*> -> {
                        val simplified = simplify(it.stmt.expr)
                        if(FrontendMetadata.getMetadataValue(it.stmt.expr, "cType").isPresent)
                            FrontendMetadata.create(simplified, "cType", CComplexType.getType(it.stmt.expr))
                        StmtLabel(Assign(cast(it.stmt.varDecl, it.stmt.varDecl.type), cast(simplified, it.stmt.varDecl.type)),  metadata = it.metadata)
                    }
                is AssumeStmt -> {
                    val simplified = simplify(it.stmt.cond)
                    if(FrontendMetadata.getMetadataValue(it.stmt.cond, "cType").isPresent) {
                        FrontendMetadata.create(simplified, "cType", CComplexType.getType(it.stmt.cond))
                    }
                    FrontendMetadata.create(simplified, "cTruth", it.stmt.cond is NeqExpr<*>)
                    StmtLabel(Assume(simplified), metadata = it.metadata)
                }
                else -> it
            } else it  }
            if(newLabels != edge.label.labels) {
                builder.removeEdge(edge)
                builder.addEdge(edge.withLabel(SequenceLabel(newLabels)))
            }
        }
        builder.metaData["simplifiedExprs"] = Unit
        return builder
    }
}