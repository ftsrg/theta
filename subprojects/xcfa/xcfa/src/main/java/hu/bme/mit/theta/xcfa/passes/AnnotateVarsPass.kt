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

import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.xcfa.model.XcfaProcedureBuilder

/**
 * Annotate each variable with its scope (procedure)
 * Sets the `annotated` flag on the ProcedureBuilder
 */
class AnnotateVarsPass : ProcedurePass {
    override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
        val varLut = LinkedHashMap<VarDecl<*>, VarDecl<*>>()
        builder.getVars().forEach { varLut.put(it, Var(builder.name + "::" + it.name, it.type)) }
        builder.changeVars(varLut)

        for (edge in ArrayList(builder.getEdges())) {
            builder.removeEdge(edge)
            builder.addEdge(edge.withLabel(edge.label.changeVars(varLut)))
        }
        builder.metaData["annotated"] = Unit
        return builder
    }
}