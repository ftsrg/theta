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

import com.google.common.collect.Sets
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.xcfa.collectVars
import hu.bme.mit.theta.xcfa.collectVarsWithAccessType
import hu.bme.mit.theta.xcfa.isRead
import hu.bme.mit.theta.xcfa.model.SequenceLabel
import hu.bme.mit.theta.xcfa.model.XcfaEdge
import hu.bme.mit.theta.xcfa.model.XcfaProcedureBuilder

/**
 * Remove unused variables from the program.
 * Requires the ProcedureBuilder to be `deterministic` (@see DeterministicPass)
 */
class UnusedVarPass(val parseContext: ParseContext, val uniqueWarningLogger: Logger) : ProcedurePass {

    override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
        checkNotNull(builder.metaData["deterministic"])

        val usedVars = LinkedHashSet<VarDecl<*>>()

        var edges = LinkedHashSet(builder.getEdges())
        lateinit var lastEdges: Set<XcfaEdge>
        do {
            lastEdges = edges

            usedVars.clear()
            builder.getEdges()
                .forEach {
                    usedVars.addAll(it.label.collectVarsWithAccessType().filter { it.value.isRead }.map { it.key })
                }

            for (edge in edges.filter { it.label.collectVars().any { !usedVars.contains(it) } }) {
                val newLabels = (edge.label as SequenceLabel).labels.mapNotNull {
                    if (it.collectVars().any { !usedVars.contains(it) }) {
                        null
                    } else it
                }
                if (newLabels != edge.label.labels) {
                    builder.removeEdge(edge)
                    val newEdge = edge.withLabel(SequenceLabel(newLabels))
                    builder.addEdge(newEdge)
                }
            }
            edges = LinkedHashSet(builder.getEdges())
        } while (lastEdges != edges)

        val allVars = Sets.union(builder.getVars(),
            builder.parent.getVars().map { it.wrappedVar }.toSet())
        val varsAndParams = Sets.union(allVars, builder.getParams().map { it.first }.toSet())
        if (!varsAndParams.containsAll(usedVars)) {
            uniqueWarningLogger.write(Logger.Level.INFO,
                "WARNING: There are some used variables not present as declarations: " +
                    "${
                        usedVars.filter {
                            !varsAndParams.contains(it)
                        }
                    }\n")
        }

        val list = builder.getVars().filter { !usedVars.contains(it) }.toList()
        list.forEach {
            builder.removeVar(it)
        }

        return builder
    }
}