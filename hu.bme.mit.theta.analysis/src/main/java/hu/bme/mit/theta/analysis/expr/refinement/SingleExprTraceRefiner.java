/*
 *  Copyright 2017 Budapest University of Technology and Economics
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

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.algorithm.ArgTrace;
import hu.bme.mit.theta.analysis.algorithm.cegar.Refiner;
import hu.bme.mit.theta.analysis.algorithm.cegar.RefinerResult;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.common.logging.Logger;

/**
 * A Refiner implementation that can refine a single trace (of ExprStates and
 * ExprActions) using an ExprTraceChecker and a PrecRefiner.
 */
public final class SingleExprTraceRefiner<S extends ExprState, A extends ExprAction, P extends Prec, R extends Refutation>
		implements Refiner<S, A, P> {

	private final ExprTraceChecker<R> exprTraceChecker;
	private final PrecRefiner<S, A, P, R> precRefiner;
	private final Logger logger;

	private SingleExprTraceRefiner(final ExprTraceChecker<R> exprTraceChecker,
			final PrecRefiner<S, A, P, R> precRefiner, final Logger logger) {
		this.exprTraceChecker = checkNotNull(exprTraceChecker);
		this.precRefiner = checkNotNull(precRefiner);
		this.logger = checkNotNull(logger);
	}

	public static <S extends ExprState, A extends ExprAction, P extends Prec, R extends Refutation> SingleExprTraceRefiner<S, A, P, R> create(
			final ExprTraceChecker<R> exprTraceChecker, final PrecRefiner<S, A, P, R> precRefiner,
			final Logger logger) {
		return new SingleExprTraceRefiner<>(exprTraceChecker, precRefiner, logger);
	}

	@Override
	public RefinerResult<S, A, P> refine(final ARG<S, A> arg, final P prec) {
		checkNotNull(arg);
		checkNotNull(prec);
		assert !arg.isSafe() : "ARG must be unsafe";

		final ArgTrace<S, A> cexToConcretize = arg.getCexs().findFirst().get();
		final Trace<S, A> traceToConcretize = cexToConcretize.toTrace();
		logger.writeln("Trace length: ", traceToConcretize.length(), 3, 2);
		logger.writeln("Trace: ", traceToConcretize, 4, 3);

		logger.write("Checking...", 3, 2);
		final ExprTraceStatus<R> cexStatus = exprTraceChecker.check(traceToConcretize);
		logger.writeln("done: ", cexStatus, 3, 0);

		assert cexStatus.isFeasible() || cexStatus.isInfeasible() : "Unknown CEX status";

		if (cexStatus.isFeasible()) {
			return RefinerResult.unsafe(traceToConcretize);
		} else {
			final R refutation = cexStatus.asInfeasible().getRefutation();
			logger.writeln(refutation, 4, 3);
			final P refinedPrec = precRefiner.refine(prec, traceToConcretize, refutation);
			final int pruneIndex = refutation.getPruneIndex();
			assert 0 <= pruneIndex : "Pruning index must be non-negative";
			assert pruneIndex <= cexToConcretize.length() : "Pruning index larger than cex length";
			logger.writeln("Pruning from index ", pruneIndex, 3, 2);

			final ArgNode<S, A> nodeToPrune = cexToConcretize.node(pruneIndex);
			arg.prune(nodeToPrune);
			return RefinerResult.spurious(refinedPrec);
		}
	}

	@Override
	public String toString() {
		return Utils.toStringBuilder(getClass().getSimpleName()).add(exprTraceChecker).add(precRefiner).toString();
	}

}
