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
import java.util.Optional

class XcfaBuilder(
        var name: String,
        private val vars: MutableSet<XcfaGlobalVar> = LinkedHashSet(),
        private val procedures: MutableSet<XcfaProcedureBuilder> = LinkedHashSet(),
        private val initProcedures: MutableList<Pair<XcfaProcedureBuilder, List<Expr<*>>>> = ArrayList()) {
    fun getVars() : Set<XcfaGlobalVar> = vars
    fun getProcedures() : Set<XcfaProcedureBuilder> = procedures
    fun getInitProcedures() : List<Pair<XcfaProcedureBuilder, List<Expr<*>>>> = initProcedures

    fun build() : XCFA {
        return XCFA(
                name=name,
                vars=vars,
                procedures=procedures.map { it.build() }.toSet(),
                initProcedures=initProcedures.map { Pair(it.first.build(), it.second) }
        )
    }

    fun addVar(toAdd: XcfaGlobalVar) {
        vars.add(toAdd)
    }

    fun addProcedure(toAdd: XcfaProcedureBuilder) {
        procedures.add(toAdd)
    }

    fun addEntryPoint(toAdd: XcfaProcedureBuilder, params: List<Expr<*>>) {
        procedures.add(toAdd)
        initProcedures.add(Pair(toAdd, params))
    }
}

class XcfaProcedureBuilder(
        var name: String,
        private val params: MutableList<Pair<VarDecl<*>, ParamDirection>> = ArrayList(),
        private val vars: MutableSet<VarDecl<*>> = LinkedHashSet(),
        private val locs: MutableSet<XcfaLocation> = LinkedHashSet(),
        private val edges: MutableSet<XcfaEdge> = LinkedHashSet()
) {
    lateinit var initLoc: XcfaLocation
    lateinit var finalLoc: Optional<XcfaLocation>
    lateinit var errorLoc: Optional<XcfaLocation>
    fun getParams() : List<Pair<VarDecl<*>, ParamDirection>> = params
    fun getVars() : Set<VarDecl<*>> = vars
    fun getLocs() : Set<XcfaLocation> = locs
    fun getEdges() : Set<XcfaEdge> = edges

    fun build() : XcfaProcedure {
        return XcfaProcedure(
                name=name,
                params=params,
                vars=vars,
                locs=locs,
                edges=edges,
                initLoc=initLoc,
                finalLoc=finalLoc,
                errorLoc=errorLoc
        )
    }

    fun addParam(toAdd: VarDecl<*>, dir: ParamDirection) {
        params.add(Pair(toAdd, dir))
    }

    fun addVar(toAdd: VarDecl<*>) {
        vars.add(toAdd)
    }

    fun addEdge(toAdd: XcfaEdge) {
        edges.add(toAdd)
    }

    fun addLoc(toAdd: XcfaLocation) {
        locs.add(toAdd)
    }
}
