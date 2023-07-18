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

package hu.bme.mit.theta.xcfa.cli.witnesses

import com.google.common.collect.Lists
import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.c2xcfa.getCMetaData
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr
import hu.bme.mit.theta.core.type.fptype.FpLitExpr
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.model.*
import java.math.BigInteger

enum class Verbosity {
    NECESSARY,
    SOURCE_EXISTS,
    STMT_EXISTS,
    EVERYTHING
}

fun traceToWitness(
    verbosity: Verbosity = Verbosity.SOURCE_EXISTS,
    trace: Trace<XcfaState<ExplState>, XcfaAction>,
    parseContext: ParseContext
): Trace<WitnessNode, WitnessEdge> {
    val newStates = ArrayList<WitnessNode>()
    val newActions = ArrayList<WitnessEdge>()

    var lastNode = WitnessNode(id = "N${newStates.size}", entry = true, sink = false,
        violation = false)
    newStates.add(lastNode)

    for (i in 0 until trace.length()) {
        val state = trace.states[i]
        val nextState = trace.states[i + 1]
        val node = WitnessNode(
            id = "N${newStates.size}",
            entry = false,
            sink = false,
            violation = state.processes.any { it.value.locs.any(XcfaLocation::error) },
            xcfaLocations = state.processes.map { Pair(it.key, it.value.locs) }.toMap(),
            cSources = state.processes.map {
                Pair(it.key, it.value.locs.map { it.getCMetaData()?.sourceText ?: "<unknown>" })
            }.toMap(),
            globalState = state.sGlobal
        )
        if (node != WitnessNode(id = "N${newStates.size}")) {
            newStates.add(node)
            val edge = WitnessEdge(sourceId = lastNode.id, targetId = node.id,
                threadId = trace.actions[i].pid.toString())
            newActions.add(edge)
            lastNode = node
        }

        val action = trace.actions[i]
        val flattenedSequence = flattenSequence(action.edge.label)
        for (xcfaLabel in flattenedSequence) {
            val node = WitnessNode(id = "N${newStates.size}", entry = false, sink = false,
                violation = false)
            val edge = labelToEdge(lastNode, node, xcfaLabel, action.pid,
                nextState.sGlobal.getVal(), parseContext)
            if (node != WitnessNode(id = "N${newStates.size}") || shouldInclude(edge, verbosity)) {
                newStates.add(node)
                newActions.add(edge)
                lastNode = node
            }
        }
    }

    val lastState = trace.states[trace.length()]
    val node = WitnessNode(
        id = "N${newStates.size}",
        entry = false,
        sink = false,
        violation = lastState.processes.any { it.value.locs.any(XcfaLocation::error) },
        xcfaLocations = lastState.processes.map { Pair(it.key, it.value.locs) }.toMap(),
        cSources = lastState.processes.map {
            Pair(it.key, it.value.locs.map { it.getCMetaData()?.sourceText ?: "<unknown>" })
        }.toMap(),
        globalState = lastState.sGlobal
    )
    newStates.add(node)
    val edge = WitnessEdge(sourceId = lastNode.id, targetId = node.id)
    newActions.add(edge)

    return Trace.of(newStates, newActions)

}

fun shouldInclude(edge: WitnessEdge, verbosity: Verbosity): Boolean =
    when (verbosity) {
        Verbosity.NECESSARY -> edge.control != null || edge.assumption != null || edge.createThread != null
        Verbosity.SOURCE_EXISTS -> shouldInclude(edge, Verbosity.NECESSARY) || edge.cSource != null
        Verbosity.STMT_EXISTS -> shouldInclude(edge, Verbosity.NECESSARY) || edge.stmt != null
        Verbosity.EVERYTHING -> true
    }


private fun labelToEdge(lastNode: WitnessNode, node: WitnessNode, xcfaLabel: XcfaLabel, pid: Int,
    valuation: Valuation, parseContext: ParseContext): WitnessEdge =
    WitnessEdge(
        sourceId = lastNode.id,
        targetId = node.id,

        assumption = if (xcfaLabel is StmtLabel && xcfaLabel.stmt is HavocStmt<*>) {
            val varDecl = (xcfaLabel.stmt as HavocStmt<*>).varDecl
            val eval = valuation.eval(varDecl)
            val splitName = varDecl.name.split("::")
            val rootName = splitName.subList(2, splitName.size).joinToString("::")
            if (parseContext.metadata.getMetadataValue(rootName, "cName").isPresent && eval.isPresent)
                "${parseContext.metadata.getMetadataValue(rootName, "cName").get()} == ${
                    printLit(eval.get())
                }"
            else null
        } else null,

        control = if (xcfaLabel is StmtLabel && xcfaLabel.choiceType != ChoiceType.NONE) {
            xcfaLabel.choiceType == ChoiceType.MAIN_PATH
        } else null,

        startline = xcfaLabel.getCMetaData()?.lineNumberStart,
        endline = xcfaLabel.getCMetaData()?.lineNumberStop,
        startoffset = xcfaLabel.getCMetaData()?.lineNumberStart,
        endoffset = xcfaLabel.getCMetaData()?.lineNumberStart,

        threadId = if (pid != null) "$pid" else null,

        stmt = if (xcfaLabel is StmtLabel) xcfaLabel.stmt.toString() else null,
        cSource = xcfaLabel.getCMetaData()?.sourceText
    )

private fun flattenSequence(label: XcfaLabel): List<XcfaLabel> =
    when (label) {
        is NondetLabel -> error("Cannot handle nondet labels in witnesses")
        is SequenceLabel -> label.labels.map { flattenSequence(it) }.flatten()
        else -> listOf(label)
    }

private fun printLit(litExpr: LitExpr<*>): String? {
    return if (litExpr is BvLitExpr) {
        val value = litExpr.value
        var intValue = BigInteger.ZERO
        for (i in value.indices) {
            val b = value[i]
            if (b) {
                intValue = intValue.add(BigInteger.ONE.shiftLeft(value.size - 1 - i))
            }
        }
        "0x" + intValue.toString(16)
    } else if (litExpr is FpLitExpr) {
        val boolList: MutableList<Boolean> = java.util.ArrayList()
        val tmpList: MutableList<Boolean> = java.util.ArrayList()
        for (b in litExpr.significand.value) {
            tmpList.add(b)
        }
        boolList.addAll(Lists.reverse(tmpList))
        tmpList.clear()
        for (b in litExpr.exponent.value) {
            tmpList.add(b)
        }
        boolList.addAll(Lists.reverse(tmpList))
        boolList.add(litExpr.hidden)
        var aggregate = 0
        val hexDigits: MutableList<Char> = java.util.ArrayList()
        for (i in boolList.indices) {
            if (i % 4 == 0 && i > 0) {
                if (aggregate < 10) hexDigits.add(
                    ('0'.code + aggregate).toChar()) else hexDigits.add(
                    ('A'.code - 10 + aggregate).toChar())
                aggregate = 0
            }
            if (boolList[i]) aggregate += 1 shl i % 4
        }
        if (aggregate < 10) hexDigits.add(('0'.code + aggregate).toChar()) else hexDigits.add(
            ('A'.code - 10 + aggregate).toChar())
        val stringBuilder = StringBuilder("0x")
        for (character in Lists.reverse(hexDigits)) {
            stringBuilder.append(character)
        }
        stringBuilder.toString()
    } else {
        litExpr.toString()
    }
}