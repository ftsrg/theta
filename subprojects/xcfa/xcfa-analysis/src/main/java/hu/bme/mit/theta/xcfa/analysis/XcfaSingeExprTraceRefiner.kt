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
import com.google.common.base.Preconditions.checkState
import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.ARG
import hu.bme.mit.theta.analysis.algorithm.cegar.RefinerResult
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.refinement.*
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.stmt.Stmts.Assume
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.anytype.IteExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.inttype.IntExprs
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.xcfa.WRITE
import hu.bme.mit.theta.xcfa.dereferencesWithAccessTypes
import hu.bme.mit.theta.xcfa.getFlatLabels
import hu.bme.mit.theta.xcfa.model.SequenceLabel
import hu.bme.mit.theta.xcfa.model.StmtLabel
import hu.bme.mit.theta.xcfa.model.XcfaLabel
import java.util.*


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

    fun refineTempHere(arg: ARG<S, A>, prec: P?): RefinerResult<S, A, P?> {
        Preconditions.checkNotNull(arg)
        Preconditions.checkNotNull(prec)
        assert(!arg.isSafe) { "ARG must be unsafe" }
        val optionalNewCex = arg.cexs.findFirst()
        val cexToConcretize = optionalNewCex.get()
        val traceToConcretize = cexToConcretize.toTrace().addDereferenceConstraints() as Trace<S, A>
        logger.write(Logger.Level.INFO, "|  |  Trace length: %d%n", traceToConcretize.length())
        logger.write(Logger.Level.DETAIL, "|  |  Trace: %s%n", traceToConcretize)
        logger.write(Logger.Level.SUBSTEP, "|  |  Checking trace...")
        val cexStatus = exprTraceChecker.check(traceToConcretize)
        logger.write(Logger.Level.SUBSTEP, "done, result: %s%n", cexStatus)
        assert(cexStatus.isFeasible() || cexStatus.isInfeasible()) { "Unknown CEX status" }
        return if (cexStatus.isFeasible()) {
            RefinerResult.unsafe(traceToConcretize)
        } else {
            val refutation = cexStatus.asInfeasible().refutation
            logger.write(Logger.Level.DETAIL, "|  |  |  Refutation: %s%n", refutation)
            val refinedPrec = precRefiner.refine(prec, traceToConcretize, refutation)
            val pruneIndex = refutation.getPruneIndex()
            assert(0 <= pruneIndex) { "Pruning index must be non-negative" }
            assert(pruneIndex <= cexToConcretize.length()) { "Pruning index larger than cex length" }
            when (pruneStrategy) {
                PruneStrategy.LAZY -> {
                    logger.write(Logger.Level.SUBSTEP, "|  |  Pruning from index %d...", pruneIndex)
                    val nodeToPrune = cexToConcretize.node(pruneIndex)
                    nodePruner.prune(arg, nodeToPrune)
                }

                PruneStrategy.FULL -> {
                    logger.write(Logger.Level.SUBSTEP, "|  |  Pruning whole ARG", pruneIndex)
                    arg.pruneAll()
                }

                else -> throw java.lang.UnsupportedOperationException("Unsupported pruning strategy")
            }
            logger.write(Logger.Level.SUBSTEP, "done%n")
            RefinerResult.spurious(refinedPrec)
        }
    }

    override fun refine(arg: ARG<S, A>, prec: P?): RefinerResult<S, A, P?> {
        Preconditions.checkNotNull(arg)
        Preconditions.checkNotNull<P>(prec)
        assert(!arg.isSafe) { "ARG must be unsafe" }

        val optionalNewCex = arg.cexs.findFirst()
        val cexToConcretize = optionalNewCex.get()
        val traceToConcretize = cexToConcretize.toTrace()

        val refinerResult = refineTempHere(arg, prec) // super.refine should be used
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

private fun <S, A> Trace<S, A>.addDereferenceConstraints(): Trace<XcfaState<*>, XcfaAction> {
    this as Trace<XcfaState<*>, XcfaAction>

    val writeTriples = LinkedHashMap<Type, MutableList<Triple<Expr<*>, Expr<*>, Expr<IntType>>>>()

    val newActions = actions.map {
        val newLabelList = ArrayList<XcfaLabel>()
        for (flatLabel in it.label.getFlatLabels()) {
            val preList = ArrayList<XcfaLabel>()
            val postList = ArrayList<XcfaLabel>()

            for ((deref, type) in flatLabel.dereferencesWithAccessTypes) {
                checkState(deref.uniquenessIdx.isPresent,
                    "Incomplete dereferences (missing uniquenessIdx) are not handled properly.")
                val list = writeTriples[deref.type] ?: emptyList()
                val expr = list.fold(Int(0) as Expr<IntType>) { elze, (arr, off, value) ->
                    IteExpr.of(And(listOf(Eq(arr, deref.array), Eq(off, deref.offset))), value, elze)
                }
                if (type == WRITE) {
                    val writeExpr = ExprUtils.simplify(IntExprs.Add(expr, Int(1)))
                    writeTriples.getOrPut(deref.type) { ArrayList() }
                        .add(Triple(deref.array, deref.offset, deref.uniquenessIdx.get()))
                    postList.add(StmtLabel(Assume(ExprUtils.simplify(Eq(writeExpr, deref.uniquenessIdx.get())))))
                } else {
                    preList.add(StmtLabel(Assume(ExprUtils.simplify(Eq(expr, deref.uniquenessIdx.get())))))
                }
            }

            newLabelList.addAll(preList)
            newLabelList.add(flatLabel)
            newLabelList.addAll(postList)
        }

        it.withLabel(SequenceLabel(newLabelList, it.label.metadata))
    }
    return Trace.of(states, newActions)
}
