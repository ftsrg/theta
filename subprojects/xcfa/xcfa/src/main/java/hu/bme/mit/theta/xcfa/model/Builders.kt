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
import hu.bme.mit.theta.xcfa.passes.procedure.*
import java.util.Optional

class XcfaBuilder(
        var name: String,
        private val vars: MutableSet<XcfaGlobalVar> = LinkedHashSet(),
        private val procedures: MutableSet<XcfaProcedureBuilder> = LinkedHashSet(),
        private val initProcedures: MutableList<Pair<XcfaProcedureBuilder, List<Expr<*>>>> = ArrayList(),
        val metaData: MutableMap<String, Any> = LinkedHashMap()) {
    fun getVars() : Set<XcfaGlobalVar> = vars
    fun getProcedures() : Set<XcfaProcedureBuilder> = procedures
    fun getInitProcedures() : List<Pair<XcfaProcedureBuilder, List<Expr<*>>>> = initProcedures

    fun build() : XCFA {
        return XCFA(
                name=name,
                vars=vars,
                procedureBuilders=procedures,
                initProcedureBuilders=initProcedures
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
        private val edges: MutableSet<XcfaEdge> = LinkedHashSet(),
        val metaData: MutableMap<String, Any> = LinkedHashMap()
) {
    lateinit var initLoc: XcfaLocation
        private set
    var finalLoc: Optional<XcfaLocation> = Optional.empty()
        private set
    var errorLoc: Optional<XcfaLocation> = Optional.empty()
        private set
    fun getParams() : List<Pair<VarDecl<*>, ParamDirection>> = params
    fun getVars() : Set<VarDecl<*>> = vars
    fun getLocs() : Set<XcfaLocation> = locs
    fun getEdges() : Set<XcfaEdge> = edges

    fun build(parent: XCFA) : XcfaProcedure {
        var that = this
        that = NormalizePass().run(that)
        that = DeterministicPass().run(that)
        that = EmptyEdgeRemovalPass().run(that)
        that = UnusedLocRemoval().run(that)
        that = ErrorLocationPass().run(that)
        return XcfaProcedure(
                parent=parent,
                name=that.name,
                params=that.params,
                vars=that.vars,
                locs=that.locs,
                edges=that.edges,
                initLoc=that.initLoc,
                finalLoc=that.finalLoc,
                errorLoc=that.errorLoc
        )
    }

    fun addParam(toAdd: VarDecl<*>, dir: ParamDirection) {
        params.add(Pair(toAdd, dir))
    }

    fun addVar(toAdd: VarDecl<*>) {
        vars.add(toAdd)
    }

    fun createErrorLoc() {
        errorLoc = Optional.of(XcfaLocation(name + "_error", error=true))
        locs.add(errorLoc.get())
    }

    fun createFinalLoc() {
        finalLoc = Optional.of(XcfaLocation(name + "_final", final=true))
        locs.add(finalLoc.get())
    }

    fun createInitLoc() {
        initLoc = XcfaLocation(name + "_init", initial=true)
        locs.add(initLoc)
    }

    fun addEdge(toAdd: XcfaEdge) {
        addLoc(toAdd.source)
        addLoc(toAdd.target)
        edges.add(toAdd)
        toAdd.source.outgoingEdges.add(toAdd)
        toAdd.target.incomingEdges.add(toAdd)
    }

    fun addLoc(toAdd: XcfaLocation) {
        if(!locs.contains(toAdd)) {
            check(!toAdd.error)
            check(!toAdd.initial)
            check(!toAdd.final)
            locs.add(toAdd)
        }
    }

    fun removeEdge(toRemove: XcfaEdge) {
        toRemove.source.outgoingEdges.remove(toRemove)
        toRemove.target.incomingEdges.remove(toRemove)
        edges.remove(toRemove)
    }

    fun removeLoc(toRemove: XcfaLocation) {
        locs.remove(toRemove)
    }

    fun removeLocs(pred: (XcfaLocation) -> Boolean) {
        while(locs.any(pred)) {
            locs.removeIf(pred)
        }
    }
}