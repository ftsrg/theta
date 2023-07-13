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
import hu.bme.mit.theta.core.type.LitExpr
import java.util.*

class XCFA(
    val name: String,
    val vars: Set<XcfaGlobalVar>,                                   // global variables
    procedureBuilders: Set<XcfaProcedureBuilder> = emptySet(),
    initProcedureBuilders: List<Pair<XcfaProcedureBuilder, List<Expr<*>>>> = emptyList()
) {

    var cachedHash: Int? = null

    var procedures: Set<XcfaProcedure> =                                // procedure definitions
        procedureBuilders.map { it.build(this) }.toSet()
        private set
    var initProcedures: List<Pair<XcfaProcedure, List<Expr<*>>>> =      // procedure names and parameter assignments
        initProcedureBuilders.map { Pair(it.first.build(this), it.second) }
        private set

    /**
     * Recreate an existing XCFA by substituting the procedures and initProcedures fields.
     */
    fun recreate(procedures: Set<XcfaProcedure>,
        initProcedures: List<Pair<XcfaProcedure, List<Expr<*>>>>
    ): XCFA {
        this.procedures = procedures
        this.initProcedures = initProcedures
        return this
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (javaClass != other?.javaClass) return false

        other as XCFA

        if (name != other.name) return false
        if (vars != other.vars) return false
        if (procedures != other.procedures) return false
        if (initProcedures != other.initProcedures) return false

        return true
    }

    override fun hashCode(): Int {
        if (cachedHash != null) return cachedHash as Int
        var result = name.hashCode()
        result = 31 * result + vars.hashCode()
        result = 31 * result + procedures.hashCode()
        result = 31 * result + initProcedures.hashCode()
        cachedHash = result
        return result
    }

    override fun toString(): String {
        return "XCFA(name='$name', vars=$vars, procedures=$procedures, initProcedures=$initProcedures)"
    }


}

data class XcfaProcedure(
    val name: String,
    val params: List<Pair<VarDecl<*>, ParamDirection>>,             // procedure params
    val vars: Set<VarDecl<*>>,                                      // local variables
    val locs: Set<XcfaLocation>,                                    // locations
    val edges: Set<XcfaEdge>,                                       // edges

    val initLoc: XcfaLocation,                                      // initial location
    val finalLoc: Optional<XcfaLocation>,                           // final location (optional)
    val errorLoc: Optional<XcfaLocation>                            // error location (optional)
) {

    internal lateinit var parent: XCFA
}

data class XcfaLocation @JvmOverloads constructor(
    val name: String,                                               // label of the location
    val initial: Boolean = false,                                   // is this the initial location?
    val final: Boolean = false,                                     // is this the final location?
    val error: Boolean = false,                                     // is this the error location?
    val metadata: MetaData = EmptyMetaData,
) {

    val incomingEdges: MutableSet<XcfaEdge> = LinkedHashSet()           // all incoming edges in the current procedure
    val outgoingEdges: MutableSet<XcfaEdge> = LinkedHashSet()           // all outgoing edges in the current procedure

    companion object {

        private var cnt: Int = 0;
        fun uniqueCounter(): Int {
            return cnt++;
        }
    }

    override fun toString(): String {
        return "$name ${if (initial) "{init}" else ""}${if (final) "{final}" else ""}${if (error) "{error}" else ""}"
    }
}

data class XcfaEdge @JvmOverloads constructor(
    val source: XcfaLocation,                                       // source location
    val target: XcfaLocation,                                       // target location
    val label: XcfaLabel = NopLabel,                                // edge label
    val metadata: MetaData = EmptyMetaData,
) {

    fun withLabel(label: XcfaLabel): XcfaEdge = XcfaEdge(source, target, label)
    fun withTarget(target: XcfaLocation): XcfaEdge = XcfaEdge(source, target, label)
    fun withSource(source: XcfaLocation): XcfaEdge = XcfaEdge(source, target, label)
}

data class XcfaGlobalVar @JvmOverloads constructor(
    val wrappedVar: VarDecl<*>,
    val initValue: LitExpr<*>,
    val threadLocal: Boolean = false
)

enum class ParamDirection {
    IN,
    OUT,
    INOUT
}
