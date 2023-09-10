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

package hu.bme.mit.theta.xcfa.model

import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.xcfa.passes.ProcedurePassManager
import java.util.*

@DslMarker
annotation class XcfaDsl

@XcfaDsl
class XcfaBuilder @JvmOverloads constructor(
    var name: String,
    private val vars: MutableSet<XcfaGlobalVar> = LinkedHashSet(),
    private val procedures: MutableSet<XcfaProcedureBuilder> = LinkedHashSet(),
    private val initProcedures: MutableList<Pair<XcfaProcedureBuilder, List<Expr<*>>>> = ArrayList(),
    val metaData: MutableMap<String, Any> = LinkedHashMap()) {

    fun getVars(): Set<XcfaGlobalVar> = vars
    fun getProcedures(): Set<XcfaProcedureBuilder> = procedures
    fun getInitProcedures(): List<Pair<XcfaProcedureBuilder, List<Expr<*>>>> = initProcedures

    fun build(): XCFA {
        return XCFA(
            name = name,
            vars = vars,
            procedureBuilders = procedures,
            initProcedureBuilders = initProcedures
        )
    }

    fun addVar(toAdd: XcfaGlobalVar) {
        vars.add(toAdd)
    }

    fun addProcedure(toAdd: XcfaProcedureBuilder) {
        procedures.add(toAdd)
        toAdd.parent = this
    }

    fun addEntryPoint(toAdd: XcfaProcedureBuilder, params: List<Expr<*>>) {
        addProcedure(toAdd)
        initProcedures.add(Pair(toAdd, params))
    }
}

@XcfaDsl
class XcfaProcedureBuilder @JvmOverloads constructor(
    var name: String,
    private val manager: ProcedurePassManager,
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
    lateinit var parent: XcfaBuilder
    private lateinit var optimized: XcfaProcedureBuilder
    private lateinit var built: XcfaProcedure
    fun getParams(): List<Pair<VarDecl<*>, ParamDirection>> = if (this::optimized.isInitialized) optimized.params else params
    fun getVars(): Set<VarDecl<*>> = if (this::optimized.isInitialized) optimized.vars else vars
    fun getLocs(): Set<XcfaLocation> = if (this::optimized.isInitialized) optimized.locs else locs
    fun getEdges(): Set<XcfaEdge> = if (this::optimized.isInitialized) optimized.edges else edges

    fun optimize() {
        if (!this::optimized.isInitialized) {
            var that = this
            for (pass in manager.passes) {
                that = pass.run(that)
            }
            optimized = that
        }
    }

    fun build(parent: XCFA): XcfaProcedure {
        if (this::built.isInitialized) return built;
        if (!this::optimized.isInitialized) optimize()
        built = XcfaProcedure(
            name = optimized.name,
            params = optimized.params,
            vars = optimized.vars,
            locs = optimized.locs,
            edges = optimized.edges,
            initLoc = optimized.initLoc,
            finalLoc = optimized.finalLoc,
            errorLoc = optimized.errorLoc
        )
        built.parent = parent
        return built
    }

    fun addParam(toAdd: VarDecl<*>, dir: ParamDirection) {
        check(
            !this::optimized.isInitialized) { "Cannot add/remove new elements after optimization passes!" }
        params.add(Pair(toAdd, dir))
        vars.add(toAdd)
    }

    fun addVar(toAdd: VarDecl<*>) {
        check(
            !this::optimized.isInitialized) { "Cannot add/remove new elements after optimization passes!" }
        vars.add(toAdd)
    }

    fun removeVar(toRemove: VarDecl<*>) {
        check(
            !this::optimized.isInitialized) { "Cannot add/remove new elements after optimization passes!" }
        vars.remove(toRemove)
    }

    @JvmOverloads
    fun createErrorLoc(metaData: MetaData = EmptyMetaData) {
        check(!this::optimized.isInitialized) { "Cannot add/remove new elements after optimization passes!" }
        if (errorLoc.isEmpty) {
            errorLoc = Optional.of(XcfaLocation(name + "_error", error = true, metadata = metaData))
            locs.add(errorLoc.get())
        }
    }

    @JvmOverloads
    fun createFinalLoc(metaData: MetaData = EmptyMetaData) {
        check(!this::optimized.isInitialized) { "Cannot add/remove new elements after optimization passes!" }
        if (finalLoc.isEmpty) {
            finalLoc = Optional.of(XcfaLocation(name + "_final", final = true, metadata = metaData))
            locs.add(finalLoc.get())
        }
    }

    @JvmOverloads
    fun createInitLoc(metaData: MetaData = EmptyMetaData) {
        check(!this::optimized.isInitialized) { "Cannot add/remove new elements after optimization passes!" }
        if (!this::initLoc.isInitialized) {
            initLoc = XcfaLocation(name + "_init", initial = true, metadata = metaData)
            locs.add(initLoc)
        }
    }

    fun addEdge(toAdd: XcfaEdge) {
        check(
            !this::optimized.isInitialized) { "Cannot add/remove new elements after optimization passes!" }
        addLoc(toAdd.source)
        addLoc(toAdd.target)
        edges.add(toAdd)
        toAdd.source.outgoingEdges.add(toAdd)
        toAdd.target.incomingEdges.add(toAdd)
    }

    fun addLoc(toAdd: XcfaLocation) {
        check(
            !this::optimized.isInitialized) { "Cannot add/remove new elements after optimization passes!" }
        if (!locs.contains(toAdd)) {
            check(!toAdd.error)
            check(!toAdd.initial)
            check(!toAdd.final)
            locs.add(toAdd)
        }
    }

    fun removeEdge(toRemove: XcfaEdge) {
        check(
            !this::optimized.isInitialized) { "Cannot add/remove new elements after optimization passes!" }
        toRemove.source.outgoingEdges.remove(toRemove)
        toRemove.target.incomingEdges.remove(toRemove)
        edges.remove(toRemove)
    }

    fun removeLoc(toRemove: XcfaLocation) {
        check(
            !this::optimized.isInitialized) { "Cannot add/remove new elements after optimization passes!" }
        locs.remove(toRemove)
    }

    fun removeLocs(pred: (XcfaLocation) -> Boolean) {
        check(
            !this::optimized.isInitialized) { "Cannot add/remove new elements after optimization passes!" }
        while (locs.any(pred)) {
            locs.removeIf(pred)
            edges.removeIf { pred(it.source) }
        }
    }

    fun changeVars(varLut: Map<VarDecl<*>, VarDecl<*>>) {
        check(
            !this::optimized.isInitialized) { "Cannot add/remove new elements after optimization passes!" }
        val savedVars = ArrayList(vars)
        vars.clear()
        savedVars.forEach { vars.add(checkNotNull(varLut[it])) }
        val savedParams = ArrayList(params)
        params.clear()
        savedParams.forEach { params.add(Pair(checkNotNull(varLut[it.first]), it.second)) }
    }
}