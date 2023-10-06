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

import hu.bme.mit.theta.analysis.expl.ExplPrec
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expl.ExplStmtTransFunc
import hu.bme.mit.theta.analysis.expr.StmtAction
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.ImmutableValuation
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.Stmt
import hu.bme.mit.theta.solver.Solver
import hu.bme.mit.theta.solver.z3.Z3SolverFactory
import hu.bme.mit.theta.xcfa.collectVars
import hu.bme.mit.theta.xcfa.collectVarsWithAccessType
import hu.bme.mit.theta.xcfa.getFlatLabels
import hu.bme.mit.theta.xcfa.isWritten
import hu.bme.mit.theta.xcfa.model.*
import java.util.*

/**
 * Unrolls loops where the number of loop executions can be determined statically.
 * The UNROLL_LIMIT refers to the number of loop executions: loops that are executed more times than this limit
 * are not unrolled.
 */
class LoopUnrollPass : ProcedurePass {

    companion object {

        var UNROLL_LIMIT = 50

        private val solver: Solver = Z3SolverFactory.getInstance().createSolver()
    }

    private val testedLoops = mutableSetOf<Loop>()

    private data class Loop(
        val loopVar: VarDecl<*>, val loopVarModifiers: List<XcfaEdge>, val loopVarInit: XcfaEdge,
        val loopCondEdge: XcfaEdge, val exitCondEdge: XcfaEdge, val loopStart: XcfaLocation,
        val loopLocs: List<XcfaLocation>, val loopEdges: List<XcfaEdge>
    ) {

        private class BasicStmtAction(private val stmt: Stmt) : StmtAction() {
            constructor(edge: XcfaEdge) : this(edge.label.toStmt())
            constructor(edges: List<XcfaEdge>) : this(SequenceLabel(edges.map { it.label }).toStmt())

            override fun getStmts() = listOf(stmt)
        }

        private fun count(transFunc: ExplStmtTransFunc): Int {
            val prec = ExplPrec.of(listOf(loopVar))
            var state = ExplState.of(ImmutableValuation.empty())
            state = transFunc.getSuccStates(state, BasicStmtAction(loopVarInit), prec).first()

            var cnt = 0
            while (!transFunc.getSuccStates(state, BasicStmtAction(loopCondEdge), prec)
                    .first().isBottom
            ) {
                cnt++
                if (cnt > UNROLL_LIMIT) return -1
                state =
                    transFunc.getSuccStates(state, BasicStmtAction(loopVarModifiers), prec).first()
            }
            return cnt
        }

        private fun XcfaLabel.removeCondition(): XcfaLabel {
            val stmtToRemove =
                getFlatLabels().find { it is StmtLabel && it.stmt is AssumeStmt && (it.collectVars() - loopVar).isEmpty() }
            return when {
                this == stmtToRemove -> NopLabel
                this is SequenceLabel -> SequenceLabel(
                    labels.map { it.removeCondition() }, metadata
                )

                else -> this
            }
        }

        private fun copyBody(builder: XcfaProcedureBuilder, startLocation: XcfaLocation, index: Int): XcfaLocation {
            val locs = loopLocs.associateWith {
                val loc = XcfaLocation("loop${index}_${it.name}")
                builder.addLoc(loc)
                loc
            }

            loopEdges.forEach {
                val newSource = if (it.source == loopStart) startLocation else checkNotNull(locs[it.source])
                val newLabel = if (it.source == loopStart) it.label.removeCondition() else it.label
                val edge = XcfaEdge(newSource, checkNotNull(locs[it.target]!!), newLabel, it.metadata)
                builder.addEdge(edge)
            }

            return checkNotNull(locs[loopStart])
        }

        fun unroll(builder: XcfaProcedureBuilder, transFunc: ExplStmtTransFunc) {
            val count = count(transFunc)
            if (count == -1) return

            (loopLocs - loopStart).forEach(builder::removeLoc)
            loopEdges.forEach(builder::removeEdge)
            builder.removeEdge(exitCondEdge)

            var startLocation = loopStart
            for (i in 0 until count) {
                startLocation = copyBody(builder, startLocation, i)
            }

            builder.addEdge(
                XcfaEdge(
                    source = startLocation,
                    target = exitCondEdge.target,
                    label = exitCondEdge.label.removeCondition(),
                    metadata = exitCondEdge.metadata
                )
            )
        }
    }

    override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
        val transFunc = ExplStmtTransFunc.create(solver, 1)
        while (true) {
            val loop = findLoop(builder.initLoc) ?: break
            loop.unroll(builder, transFunc)
            testedLoops.add(loop)
        }
        return builder
    }

    private fun findLoop(initLoc: XcfaLocation): Loop? { // DFS
        val stack = Stack<XcfaLocation>()
        val explored = mutableSetOf<XcfaEdge>()
        stack.push(initLoc)
        while (stack.isNotEmpty()) {
            val current = stack.peek()
            val edgesToExplore = current.outgoingEdges subtract explored
            if (edgesToExplore.isEmpty()) {
                stack.pop()
            } else {
                val edge = edgesToExplore.random()
                if (edge.target in stack) { // loop found
                    isUnrollable(edge.target, stack)?.let { return it }
                } else {
                    stack.push(edge.target)
                }
                explored.add(edge)
            }
        }
        return null
    }

    private fun isUnrollable(loopStart: XcfaLocation, stack: Stack<XcfaLocation>): Loop? {
        if (loopStart.outgoingEdges.size != 2) return null
        val loopLocations = stack.slice(stack.lastIndexOf(loopStart) until stack.size)
        val loopEdges = loopLocations.flatMap { loc ->
            if (loc == loopStart) {
                val loopEdge = loc.outgoingEdges.filter { it.target in loopLocations }
                if (loopEdge.size != 1) return null
                loopEdge
            } else {
                if (!loopLocations.containsAll(loc.outgoingEdges.map { it.target })) {
                    return null
                }
                loc.outgoingEdges
            }
        }

        val loopVar = loopStart.outgoingEdges.map {
            val vars = it.label.collectVarsWithAccessType()
            if (vars.size != 1) return null
            vars.keys.first()
        }.reduce { v1, v2 -> if (v1 != v2) return null else v1 }

        var edge = loopStart.outgoingEdges.find { it.target in loopLocations }!!
        val necessaryLoopEdges = mutableSetOf(edge)
        while (edge.target.outgoingEdges.size == 1) {
            edge = edge.target.outgoingEdges.first()
            necessaryLoopEdges.add(edge)
        }
        val finalEdges = loopStart.incomingEdges.filter { it.source in loopLocations }
        if (finalEdges.size == 1) {
            edge = finalEdges.first()
            necessaryLoopEdges.add(edge)
            while (edge.source.incomingEdges.size == 1) {
                edge = edge.source.incomingEdges.first()
                necessaryLoopEdges.add(edge)
            }
        }

        val loopVarModifiers = loopEdges.filter {
            val vars = it.label.collectVarsWithAccessType()
            if (vars[loopVar].isWritten) {
                if (it !in necessaryLoopEdges || vars.size > 1) return null
                true
            } else {
                false
            }
        }

        lateinit var loopVarInit: XcfaEdge
        var loc = loopStart
        while (true) {
            val inEdges = loc.incomingEdges.filter { it.source !in loopLocations }
            if (inEdges.size != 1) return null
            val inEdge = inEdges.first()
            val vars = inEdge.label.collectVarsWithAccessType()
            if (vars[loopVar].isWritten) {
                if (vars.size > 1) return null
                loopVarInit = inEdge
                break
            }
            loc = inEdge.source
        }

        return Loop(
            loopVar = loopVar,
            loopVarModifiers = loopVarModifiers,
            loopVarInit = loopVarInit,
            loopCondEdge = loopStart.outgoingEdges.find { it.target in loopLocations }!!,
            exitCondEdge = loopStart.outgoingEdges.find { it.target !in loopLocations }!!,
            loopStart = loopStart,
            loopLocs = loopLocations,
            loopEdges = loopEdges
        ).also { if (it in testedLoops) return null }
    }
}