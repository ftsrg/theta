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

package hu.bme.mit.theta.xcfa.model

import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import java.util.Optional

class XCFA(
        val name: String,
        val vars: Set<XcfaGlobalVar>,                                   // global variables
        procedureBuilders: Set<XcfaProcedureBuilder>,
        initProcedureBuilders: List<Pair<XcfaProcedureBuilder, List<Expr<*>>>>
) {
    val procedures: Set<XcfaProcedure> =                                // procedure definitions
            procedureBuilders.map { it.build(this) }.toSet()
    val initProcedures: List<Pair<XcfaProcedure, List<Expr<*>>>> =      // procedure names and parameter assignments
            initProcedureBuilders.map { Pair(it.first.build(this), it.second) }
}

data class XcfaProcedure(
        val parent: XCFA,                                               // the container
        val name: String,
        val params: List<Pair<VarDecl<*>, ParamDirection>>,             // procedure params
        val vars: Set<VarDecl<*>>,                                      // local variables
        val locs: Set<XcfaLocation>,                                    // locations
        val edges: Set<XcfaEdge>,                                       // edges

        val initLoc: XcfaLocation,                                      // initial location
        val finalLoc: Optional<XcfaLocation>,                           // final location (optional)
        val errorLoc: Optional<XcfaLocation>                            // error location (optional)
)

data class XcfaLocation(
        val name: String,                                               // label of the location
        val initial: Boolean = false,                                   // is this the initial location?
        val final: Boolean = false,                                     // is this the final location?
        val error: Boolean = false,                                     // is this the error location?
) {
    val incomingEdges: MutableSet<XcfaEdge> = LinkedHashSet()           // all incoming edges in the current procedure
    val outgoingEdges: MutableSet<XcfaEdge> = LinkedHashSet()           // all outgoing edges in the current procedure
    companion object {
        private var cnt: Int = 0;
        fun uniqueCounter(): Int {
            return cnt++;
        }
    }
}

data class XcfaEdge(
        val source: XcfaLocation,                                       // source location
        val target: XcfaLocation,                                       // target location
        val label: XcfaLabel = NopLabel                                 // edge label
) {
    fun withLabel(label: XcfaLabel): XcfaEdge = XcfaEdge(source, target, label)
}

data class XcfaGlobalVar(
        val wrappedVar: VarDecl<*>,
        val initValue: LitExpr<*>,
        val threadLocal: Boolean = false
)

enum class ParamDirection {
    IN,
    OUT,
    INOUT
}
