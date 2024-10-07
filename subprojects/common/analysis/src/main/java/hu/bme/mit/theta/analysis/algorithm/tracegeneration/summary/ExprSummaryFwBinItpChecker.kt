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
import com.google.common.collect.ImmutableList
import hu.bme.mit.theta.analysis.Action
import hu.bme.mit.theta.analysis.State
import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.tracegeneration.summary.AbstractTraceSummary
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.PathUtils
import hu.bme.mit.theta.core.utils.indexings.VarIndexing
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory
import hu.bme.mit.theta.solver.ItpSolver

/**
 * ExprTraceChecker modified to concretize summaries (interconnected traces) instead of a single trace.
 * It generates a binary interpolant by incrementally checking the traces forward.
 */
class ExprSummaryFwBinItpChecker private constructor(
    init: Expr<BoolType>, target: Expr<BoolType>,
    solver: ItpSolver
) {
    private val solver: ItpSolver = Preconditions.checkNotNull(solver)
    private val init: Expr<BoolType> = Preconditions.checkNotNull(init)
    private val target: Expr<BoolType> = Preconditions.checkNotNull(target)

    fun check(
        summary: AbstractTraceSummary<out State, out Action>
    ): ExprTraceStatus<ItpRefutation?> {
        Preconditions.checkNotNull(summary)
        val summaryNodeCount = summary.summaryNodes.size

        val indexings: MutableList<VarIndexing> = ArrayList(summaryNodeCount)
        indexings.add(VarIndexingFactory.indexing(0))

        solver.push()

        val A = solver.createMarker()
        val B = solver.createMarker()
        val pattern = solver.createBinPattern(A, B)

        var nPush = 1
        solver.add(A, PathUtils.unfold(init, indexings[0]))
        solver.add(A, PathUtils.unfold(summary.initNode.findCovered .getState(0)!!.toExpr(), indexings[0]))
        assert(solver.check().isSat) { "Initial state of the trace is not feasible" }
        var satPrefix = 0

        for (i in 1 until summaryNodeCount) {
            solver.push()
            ++nPush
            indexings.add(indexings[i - 1].add(summary.getAction(i - 1)!!.nextIndexing()))
            solver.add(
                A, PathUtils.unfold(
                    summary.getState(i)!!.toExpr(),
                    indexings[i]
                )
            )
            solver.add(
                A, PathUtils.unfold(
                    summary.getAction(i - 1)!!.toExpr(),
                    indexings[i - 1]
                )
            )

            if (solver.check().isSat) {
                satPrefix = i
            } else {
                solver.pop()
                --nPush
                break
            }
        }

        val concretizable: Boolean

        if (satPrefix == summaryNodeCount - 1) {
            solver.add(B, PathUtils.unfold(target, indexings[summaryNodeCount - 1]))
            concretizable = solver.check().isSat
        } else {
            solver.add(
                B, PathUtils.unfold(
                    summary.getState(satPrefix + 1)!!.toExpr(),
                    indexings[satPrefix + 1]
                )
            )
            solver.add(
                B,
                PathUtils.unfold(
                    summary.getAction(satPrefix)!!.toExpr(),
                    indexings[satPrefix]
                )
            )
            solver.check()
            assert(solver.status.isUnsat) { "Trying to interpolate a feasible formula" }
            concretizable = false
        }

        var status: ExprTraceStatus<ItpRefutation>? = null
        if (concretizable) {
            val model = solver.model
            val builder = ImmutableList.builder<Valuation>()
            for (indexing in indexings) {
                builder.add(PathUtils.extractValuation(model, indexing))
            }
            status = ExprTraceStatus.feasible(Trace.of(builder.build(), summary.actions))
        } else {
            val interpolant = solver.getInterpolant(pattern)
            val itpFolded = PathUtils.foldin(
                interpolant.eval(A),
                indexings[satPrefix]
            )
            status = ExprTraceStatus.infeasible(
                ItpRefutation.binary(itpFolded, satPrefix, summaryNodeCount)
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
            target: Expr<BoolType>,
            solver: ItpSolver
        ): ExprSummaryFwBinItpChecker {
            return ExprSummaryFwBinItpChecker(init, target, solver)
        }
    }
}