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
package hu.bme.mit.theta.xcfa.analysis

import com.google.common.base.Preconditions
import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.ARG
import hu.bme.mit.theta.analysis.algorithm.cegar.RefinerResult
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.refinement.*
import hu.bme.mit.theta.common.logging.Logger
import java.util.LinkedList


class XcfaSingleExprTraceRefiner<S : ExprState, A : ExprAction, P : Prec, R : Refutation> :
    SingleExprTraceRefiner<S, A, P, R> {

    private constructor(
        exprTraceChecker: ExprTraceChecker<R>,
        precRefiner: PrecRefiner<S, A, P, R>,
        pruneStrategy: PruneStrategy,
        logger: Logger
    ) : super(exprTraceChecker, precRefiner, pruneStrategy, logger)

    private constructor(
        exprTraceChecker: ExprTraceChecker<R>,
        precRefiner: PrecRefiner<S, A, P, R>,
        pruneStrategy: PruneStrategy,
        logger: Logger,
        nodePruner: NodePruner<S, A>
    ) : super(exprTraceChecker, precRefiner, pruneStrategy, logger, nodePruner)

    private fun findPoppedState(trace: Trace<S, A>): Pair<Int, XcfaState<S>>? {
        trace.states.forEachIndexed { i, s ->
            val state = s as XcfaState<S>
            state.processes.entries.find { (_, processState) -> processState.popped != null }
                ?.let { (pid, processState) ->
                    val stackBeforePop = LinkedList(processState.locs)
                    stackBeforePop.push(processState.popped)
                    val processesBeforePop = state.processes.toMutableMap()
                    processesBeforePop[pid] = processState.copy(locs = stackBeforePop)
                    val stateBeforePop = state.copy(processes = processesBeforePop)
                    return Pair(i, stateBeforePop)
                }
        }
        return null
    }

    override fun refine(arg: ARG<S, A>, prec: P?): RefinerResult<S, A, P?> {
        Preconditions.checkNotNull(arg)
        Preconditions.checkNotNull<P>(prec)
        assert(!arg.isSafe) { "ARG must be unsafe" }

        val optionalNewCex = arg.cexs.findFirst()
        val cexToConcretize = optionalNewCex.get()
        val traceToConcretize = cexToConcretize.toTrace()

        val refinerResult = super.refine(arg, prec)
        val checkForPop = !(traceToConcretize.states.first() as XcfaState<*>).xcfa!!.isInlined

        return if (checkForPop && refinerResult.isUnsafe) findPoppedState(traceToConcretize)?.let { (i, state) ->
            when (pruneStrategy) {
                PruneStrategy.LAZY -> {
                    logger.write(Logger.Level.SUBSTEP, "|  |  Pruning from index %d...", i)
                    val nodeToPrune = cexToConcretize.node(i)
                    nodePruner.prune(arg, nodeToPrune)
                }

                PruneStrategy.FULL -> {
                    logger.write(Logger.Level.SUBSTEP, "|  |  Pruning whole ARG", i)
                    arg.pruneAll()
                }

                else -> throw UnsupportedOperationException("Unsupported pruning strategy")
            }

            val refinedPrec = (prec as XcfaPrec<P>).copy()
            refinedPrec.noPop.add(state)
            RefinerResult.spurious(refinedPrec as P?)
        } ?: refinerResult else refinerResult
    }

    companion object {

        fun <S : ExprState, A : ExprAction, P : Prec, R : Refutation> create(
            exprTraceChecker: ExprTraceChecker<R>, precRefiner: PrecRefiner<S, A, P, R>,
            pruneStrategy: PruneStrategy, logger: Logger
        ): XcfaSingleExprTraceRefiner<S, A, P, R> {
            return XcfaSingleExprTraceRefiner(exprTraceChecker, precRefiner, pruneStrategy, logger)
        }

        fun <S : ExprState, A : ExprAction, P : Prec, R : Refutation> create(
            exprTraceChecker: ExprTraceChecker<R>, precRefiner: PrecRefiner<S, A, P, R>,
            pruneStrategy: PruneStrategy, logger: Logger, nodePruner: NodePruner<S, A>
        ): XcfaSingleExprTraceRefiner<S, A, P, R> {
            return XcfaSingleExprTraceRefiner(exprTraceChecker, precRefiner, pruneStrategy, logger, nodePruner)
        }
    }
}
