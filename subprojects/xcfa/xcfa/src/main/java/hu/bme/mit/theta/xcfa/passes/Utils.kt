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

import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.*
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.xcfa.getFlatLabels
import hu.bme.mit.theta.xcfa.model.*
import java.util.*

fun label2edge(edge: XcfaEdge, label: XcfaLabel) {
    val source = edge.source
    val target = edge.target

}

/**
 * XcfaEdge must be in a `deterministic` ProcedureBuilder
 */
fun XcfaEdge.splitIf(function: (XcfaLabel) -> Boolean): List<XcfaEdge> {
    check(label is SequenceLabel)
    val newLabels = ArrayList<SequenceLabel>()
    var current = ArrayList<XcfaLabel>()
    for (label in label.labels) {
        if (function(label)) {
            if (current.size > 0) {
                newLabels.add(SequenceLabel(current))
                current = ArrayList()
            }
            newLabels.add(SequenceLabel(listOf(label)))
        } else {
            current.add(label)
        }
    }
    if (current.size > 0) newLabels.add(SequenceLabel(current))

    val locations = ArrayList<XcfaLocation>()
    locations.add(source)
    for (i in 2..(newLabels.size)) {
        locations.add(XcfaLocation("loc" + XcfaLocation.uniqueCounter()))
    }
    locations.add(target)

    val newEdges = ArrayList<XcfaEdge>()
    for ((i, label) in newLabels.withIndex()) {
        newEdges.add(XcfaEdge(locations[i], locations[i + 1], label))
    }
    return newEdges
}

fun Stmt.flatten(): List<Stmt> {
    return when (this) {
        is SequenceStmt -> stmts.map { it.flatten() }.flatten()
        is NonDetStmt -> error("Not possible")
        else -> listOf(this)
    }
}

@JvmOverloads
fun XcfaLabel.changeVars(varLut: Map<out Decl<*>, VarDecl<*>>, parseContext: ParseContext? = null): XcfaLabel =
    if (varLut.isNotEmpty())
        when (this) {
            is InvokeLabel -> InvokeLabel(name, params.map { it.changeVars(varLut, parseContext) },
                metadata = metadata)

            is JoinLabel -> JoinLabel(pidVar.changeVars(varLut), metadata = metadata)
            is NondetLabel -> NondetLabel(labels.map { it.changeVars(varLut, parseContext) }.toSet(),
                metadata = metadata)

            is ReadLabel -> ReadLabel(local.changeVars(varLut), global.changeVars(varLut), labels,
                metadata = metadata)

            is SequenceLabel -> SequenceLabel(labels.map { it.changeVars(varLut, parseContext) },
                metadata = metadata)

            is StartLabel -> StartLabel(name, params.map { it.changeVars(varLut, parseContext) },
                pidVar.changeVars(varLut), metadata = metadata)

            is StmtLabel -> StmtLabel(stmt.changeVars(varLut, parseContext), metadata = metadata)
            is WriteLabel -> WriteLabel(local.changeVars(varLut), global.changeVars(varLut), labels,
                metadata = metadata)

            is ReturnLabel -> ReturnLabel(enclosedLabel.changeVars(varLut))

            else -> this
        }
    else this

@JvmOverloads
fun Stmt.changeVars(varLut: Map<out Decl<*>, VarDecl<*>>, parseContext: ParseContext? = null): Stmt {
    val stmt = when (this) {
        is AssignStmt<*> -> AssignStmt.of(cast(varDecl.changeVars(varLut), varDecl.type),
            cast(expr.changeVars(varLut, parseContext), varDecl.type))

        is HavocStmt<*> -> HavocStmt.of(varDecl.changeVars(varLut))
        is AssumeStmt -> AssumeStmt.of(cond.changeVars(varLut, parseContext))
        is SequenceStmt -> SequenceStmt.of(stmts.map { it.changeVars(varLut, parseContext) })
        is SkipStmt -> this
        else -> TODO("Not yet implemented")
    }
    val metadataValue = parseContext?.getMetadata()?.getMetadataValue(this, "sourceStatement")
    if (metadataValue?.isPresent == true)
        parseContext.getMetadata().create(stmt, "sourceStatement", metadataValue.get())
    return stmt
}

@JvmOverloads
fun <T : Type> Expr<T>.changeVars(varLut: Map<out Decl<*>, VarDecl<*>>, parseContext: ParseContext? = null): Expr<T> =
    if (this is RefExpr<T>) (decl as Decl<T>).changeVars(varLut).ref
    else {
        val ret = this.withOps(this.ops.map { it.changeVars(varLut, parseContext) })
        if (parseContext?.metadata?.getMetadataValue(this, "cType")?.isPresent == true) {
            parseContext.metadata?.create(ret, "cType", CComplexType.getType(this, parseContext))
        }
        ret
    }

fun <T : Type> Decl<T>.changeVars(varLut: Map<out Decl<*>, VarDecl<*>>): VarDecl<T> =
    (varLut[this] ?: this) as VarDecl<T>

fun XcfaProcedureBuilder.canInline(): Boolean = canInline(LinkedList())
private fun XcfaProcedureBuilder.canInline(tally: LinkedList<String>): Boolean {
    if (metaData["recursive"] != null) return false
    if (metaData["canInline"] != null) return true

    tally.push(name)
    val recursive = getEdges()
        .asSequence()
        .map { it.getFlatLabels() }.flatten()
        .filterIsInstance<InvokeLabel>()
        .mapNotNull { parent.getProcedures().find { proc -> proc.name == it.name } }
        .any { tally.contains(it.name) || !it.canInline(tally) }
    tally.pop()
    metaData[if (recursive) "recursive" else "canInline"] = Unit
    return !recursive
}