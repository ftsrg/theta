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
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.xcfa.collectVarsWithAccessType
import hu.bme.mit.theta.xcfa.isRead
import hu.bme.mit.theta.xcfa.model.*

/**
 * Remove unused writes from the program.
 * Requires the ProcedureBuilder to be `deterministic` (@see DeterministicPass)
 */
class UnusedWriteRemovalPass : ProcedurePass {

    override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
        checkNotNull(builder.metaData["deterministic"])

        val usedVars = mutableSetOf<VarDecl<*>>()
        builder.getEdges().forEach {
            it.label.collectVarsWithAccessType().forEach { (varDecl, access) ->
                if (access.isRead) usedVars.add(varDecl)
            }
        }
        val unusedVars = builder.getVars() subtract usedVars subtract builder.getParams().map { it.first }.toSet()

        builder.getEdges().toList().forEach { edge ->
            val newLabel = edge.label.removeUnusedWrites(unusedVars)
            builder.removeEdge(edge)
            builder.addEdge(edge.withLabel(newLabel))
        }

        return builder
    }
}