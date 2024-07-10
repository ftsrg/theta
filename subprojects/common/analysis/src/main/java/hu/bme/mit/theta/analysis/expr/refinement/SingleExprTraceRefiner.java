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
package hu.bme.mit.theta.analysis.expr.refinement;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.arg.ARG;
import hu.bme.mit.theta.analysis.algorithm.arg.ArgNode;
import hu.bme.mit.theta.analysis.algorithm.arg.ArgTrace;
import hu.bme.mit.theta.analysis.algorithm.cegar.Refiner;
import hu.bme.mit.theta.analysis.algorithm.cegar.RefinerResult;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.Logger.Level;

import java.util.Optional;

import static com.google.common.base.Preconditions.checkNotNull;

/**
 * A Refiner implementation that can refine a single trace (of ExprStates and
 * ExprActions) using an ExprTraceChecker and a PrecRefiner.
 */
public class SingleExprTraceRefiner<S extends ExprState, A extends ExprAction, P extends Prec, R extends Refutation>
        implements Refiner<S, A, P> {
    protected final ExprTraceChecker<R> exprTraceChecker;
    protected final PrecRefiner<S, A, P, R> precRefiner;
    protected final PruneStrategy pruneStrategy;
    protected final NodePruner<S, A> nodePruner;
    protected final Logger logger;

    protected SingleExprTraceRefiner(final ExprTraceChecker<R> exprTraceChecker,
                                     final PrecRefiner<S, A, P, R> precRefiner,
                                     final PruneStrategy pruneStrategy, final Logger logger) {
        this.exprTraceChecker = checkNotNull(exprTraceChecker);
        this.precRefiner = checkNotNull(precRefiner);
        this.pruneStrategy = checkNotNull(pruneStrategy);
        this.nodePruner = ARG::prune;
        this.logger = checkNotNull(logger);
    }

    protected SingleExprTraceRefiner(final ExprTraceChecker<R> exprTraceChecker,
                                     final PrecRefiner<S, A, P, R> precRefiner,
                                     final PruneStrategy pruneStrategy, final Logger logger,
                                     final NodePruner<S, A> nodePruner) {
        this.exprTraceChecker = checkNotNull(exprTraceChecker);
        this.precRefiner = checkNotNull(precRefiner);
        this.pruneStrategy = checkNotNull(pruneStrategy);
        this.nodePruner = checkNotNull(nodePruner);
        this.logger = checkNotNull(logger);
    }

    public static <S extends ExprState, A extends ExprAction, P extends Prec, R extends Refutation> SingleExprTraceRefiner<S, A, P, R> create(
            final ExprTraceChecker<R> exprTraceChecker, final PrecRefiner<S, A, P, R> precRefiner,
            final PruneStrategy pruneStrategy, final Logger logger) {
        return new SingleExprTraceRefiner<>(exprTraceChecker, precRefiner, pruneStrategy, logger);
    }

    public static <S extends ExprState, A extends ExprAction, P extends Prec, R extends Refutation> SingleExprTraceRefiner<S, A, P, R> create(
            final ExprTraceChecker<R> exprTraceChecker, final PrecRefiner<S, A, P, R> precRefiner,
            final PruneStrategy pruneStrategy, final Logger logger, final NodePruner<S, A> nodePruner) {
        return new SingleExprTraceRefiner<>(exprTraceChecker, precRefiner, pruneStrategy, logger, nodePruner);
    }

    @Override
    public RefinerResult<S, A, P> refine(final ARG<S, A> arg, final P prec) {
        checkNotNull(arg);
        checkNotNull(prec);
        assert !arg.isSafe() : "ARG must be unsafe";

        Optional<ArgTrace<S, A>> optionalNewCex = arg.getCexs().findFirst();
        final ArgTrace<S, A> cexToConcretize = optionalNewCex.get();

        final Trace<S, A> traceToConcretize = cexToConcretize.toTrace();
        logger.write(Level.INFO, "|  |  Trace length: %d%n", traceToConcretize.length());
        logger.write(Level.DETAIL, "|  |  Trace: %s%n", traceToConcretize);

        logger.write(Level.SUBSTEP, "|  |  Checking trace...");
        final ExprTraceStatus<R> cexStatus = exprTraceChecker.check(traceToConcretize);
        logger.write(Level.SUBSTEP, "done, result: %s%n", cexStatus);

        assert cexStatus.isFeasible() || cexStatus.isInfeasible() : "Unknown CEX status";

        if (cexStatus.isFeasible()) {
            return RefinerResult.unsafe(traceToConcretize);
        } else {
            final R refutation = cexStatus.asInfeasible().getRefutation();
            logger.write(Level.DETAIL, "|  |  |  Refutation: %s%n", refutation);
            final P refinedPrec = precRefiner.refine(prec, traceToConcretize, refutation);
            final int pruneIndex = refutation.getPruneIndex();
            assert 0 <= pruneIndex : "Pruning index must be non-negative";
            assert pruneIndex <= cexToConcretize.length() : "Pruning index larger than cex length";

            switch (pruneStrategy) {
                case LAZY:
                    logger.write(Level.SUBSTEP, "|  |  Pruning from index %d...", pruneIndex);
                    final ArgNode<S, A> nodeToPrune = cexToConcretize.node(pruneIndex);
                    nodePruner.prune(arg, nodeToPrune);
                    break;
                case FULL:
                    logger.write(Level.SUBSTEP, "|  |  Pruning whole ARG", pruneIndex);
                    arg.pruneAll();
                    break;
                default:
                    throw new UnsupportedOperationException("Unsupported pruning strategy");
            }
            logger.write(Level.SUBSTEP, "done%n");

            return RefinerResult.spurious(refinedPrec);
        }
    }

    @Override
    public String toString() {
        return Utils.lispStringBuilder(getClass().getSimpleName()).add(exprTraceChecker).add(precRefiner).toString();
    }

}
