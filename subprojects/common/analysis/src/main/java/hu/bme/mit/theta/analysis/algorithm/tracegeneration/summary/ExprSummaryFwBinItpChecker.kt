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
package hu.bme.mit.theta.analysis.expr.refinement

import com.google.common.base.Preconditions
import com.google.common.base.Preconditions.checkState
import hu.bme.mit.theta.analysis.algorithm.tracegeneration.summary.AbstractTraceSummary
import hu.bme.mit.theta.analysis.algorithm.tracegeneration.summary.ConcreteSummaryBuilder
import hu.bme.mit.theta.analysis.algorithm.tracegeneration.summary.SummaryEdge
import hu.bme.mit.theta.analysis.algorithm.tracegeneration.summary.SummaryNode
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.PathUtils
import hu.bme.mit.theta.core.utils.indexings.VarIndexing
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory
import hu.bme.mit.theta.solver.ItpMarker
import hu.bme.mit.theta.solver.ItpSolver
import java.util.*

/**
 * ExprTraceChecker modified to concretize summaries (interconnected traces) instead of a single trace.
 * It generates a binary interpolant by incrementally checking the traces forward.
 */
class ExprSummaryFwBinItpChecker private constructor(
    init: Expr<BoolType>,
    solver: ItpSolver
) {
    private val solver: ItpSolver = Preconditions.checkNotNull(solver)
    private val init: Expr<BoolType> = Preconditions.checkNotNull(init)
    private var nPush: Long = 0

    // TODO what presumptions do we have about state and trace feasibility? Does it matter?
    // TODO will binitp work? see notes
    /**
     * @return a summary edge, which, if present, represents the step where we start to have infeasibility,
     * and map of the updated indexings
     */
    fun addNodeToSolver(
        currentNode: SummaryNode<ExprState, ExprAction>,
        A: ItpMarker,
        indexingMap: MutableMap<SummaryNode<ExprState, ExprAction>, VarIndexing>,
    ) : Pair<Optional<SummaryEdge<ExprState, ExprAction>>, MutableMap<SummaryNode<ExprState, ExprAction>, VarIndexing>> {
        var currentIndexingMap : MutableMap<SummaryNode<ExprState, ExprAction>, VarIndexing> = indexingMap

        for (edge in currentNode.outEdges) {
            solver.push()
            nPush++

            currentIndexingMap[edge.target] = currentIndexingMap[edge.source]!!.add(edge.action.nextIndexing())
            solver.add(
                A, PathUtils.unfold(
                    edge.target.leastOverApproximatedNode.state.toExpr(),
                    currentIndexingMap[edge.target]
                )
            )
            solver.add(
                A, PathUtils.unfold(
                    edge.action.toExpr(),
                    currentIndexingMap[edge.source]
                )
            )
            if (solver.check().isSat) {
                val result = addNodeToSolver(edge.target, A, currentIndexingMap)
                currentIndexingMap = result.second

                if (result.first.isPresent) { // reached unsat?
                    // in one of the recursive calls, reached unsat step (see else branch below)
                    return Pair(result.first, currentIndexingMap)
                }
            } else {
                solver.pop()
                nPush--
                return Pair(Optional.of(edge), currentIndexingMap)
            }
        }

        // we recursively went down on this branch, time to go one up
        return Pair(Optional.empty(), currentIndexingMap)
    }

    fun check(
        summary: AbstractTraceSummary<ExprState, ExprAction>
    ): ExprTraceStatus<ItpRefutation?> {
        Preconditions.checkNotNull(summary)
        val summaryNodeCount = summary.summaryNodes.size

        val indexingMap : MutableMap<SummaryNode<ExprState, ExprAction>, VarIndexing> = mutableMapOf()
        indexingMap[summary.initNode] = VarIndexingFactory.indexing(0)

        solver.push()
        nPush++

        val A = solver.createMarker()
        val B = solver.createMarker()
        val pattern = solver.createBinPattern(A, B)

        solver.add(A, PathUtils.unfold(init, indexingMap[summary.initNode]))
        solver.add(A, PathUtils.unfold(summary.initNode.leastOverApproximatedNode.state!!.toExpr(), indexingMap[summary.initNode]))
        assert(solver.check().isSat) { "Initial state of the trace is not feasible" }

        // iterate through summary - take care of branchings
        val result = addNodeToSolver(summary.initNode, A, indexingMap)
        val updatedIndexingMap = result.second
        val concretizable = result.first.isEmpty

        // concretizable case: we don't have a target, thus we don't even need B in this case
        if(!concretizable) {
            checkState(result.first.isPresent, "If summary not concretizable, border edge must be present!")
            val borderEdge = result.first.get()

            solver.add(
                    B, PathUtils.unfold(
                        borderEdge.target.leastOverApproximatedNode.state.toExpr(),
                        updatedIndexingMap[borderEdge.target]
                    )
                )
            solver.add(
                B,
                PathUtils.unfold(borderEdge.action.toExpr(), updatedIndexingMap[borderEdge.source])
            )
            solver.check()
            checkState(solver.status.isUnsat, "Trying to interpolate a feasible formula")
        }

        if (concretizable) {
            val model = solver.model
            val valuations = mutableMapOf<SummaryNode<ExprState, ExprAction>, Valuation>()
            for ((node, indexing) in updatedIndexingMap.entries) {
                valuations[node] = PathUtils.extractValuation(model, indexing)
            }

            val builder = ConcreteSummaryBuilder<ExprAction>()
            val concreteSummary = builder.build<ExprState>(valuations, summary)
        } else {
            
            val interpolant = solver.getInterpolant(pattern)
            val itpFolded: Expr<BoolType> = PathUtils.foldin<BoolType>(
                interpolant.eval(A),
                indexings.get(satPrefix)
            )
            status = ExprTraceStatus.infeasible<ItpRefutation?>(
                ItpRefutation.binary(itpFolded, satPrefix, stateCount)
            )
        }
        checkNotNull(status)

        solver.pop(nPush)

        return status
    }

    override fun toString(): String {
        return javaClass.simpleName
    }

    companion object {

        fun create(
            init: Expr<BoolType>,
            solver: ItpSolver
        ): ExprSummaryFwBinItpChecker {
            return ExprSummaryFwBinItpChecker(init, solver)
        }
    }
}