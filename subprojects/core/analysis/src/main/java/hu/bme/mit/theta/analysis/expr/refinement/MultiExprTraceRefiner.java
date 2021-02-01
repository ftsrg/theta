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

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.algorithm.ArgTrace;
import hu.bme.mit.theta.analysis.algorithm.cegar.Refiner;
import hu.bme.mit.theta.analysis.algorithm.cegar.RefinerResult;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.Logger.Level;

public final class MultiExprTraceRefiner<S extends ExprState, A extends ExprAction, P extends Prec, R extends Refutation>
		implements Refiner<S, A, P> {

	private final ExprTraceChecker<R> exprTraceChecker;
	private final PrecRefiner<S, A, P, R> precRefiner;
	private final PruneStrategy pruneStrategy;
	private final Logger logger;

	private MultiExprTraceRefiner(final ExprTraceChecker<R> exprTraceChecker,
								  final PrecRefiner<S, A, P, R> precRefiner,
								  final PruneStrategy pruneStrategy, final Logger logger) {
		this.exprTraceChecker = checkNotNull(exprTraceChecker);
		this.precRefiner = checkNotNull(precRefiner);
		this.pruneStrategy = checkNotNull(pruneStrategy);
		this.logger = checkNotNull(logger);
	}

	public static <S extends ExprState, A extends ExprAction, P extends Prec, R extends Refutation> MultiExprTraceRefiner<S, A, P, R> create(
			final ExprTraceChecker<R> exprTraceChecker, final PrecRefiner<S, A, P, R> precRefiner,
			final PruneStrategy pruneStrategy, final Logger logger) {
		return new MultiExprTraceRefiner<>(exprTraceChecker, precRefiner, pruneStrategy, logger);
	}

	@Override
	public RefinerResult<S, A, P> refine(final ARG<S, A> arg, final P prec) {
		checkNotNull(arg);
		checkNotNull(prec);
		assert !arg.isSafe() : "ARG must be unsafe";

		final List<ArgTrace<S, A>> cexs = arg.getCexs().collect(Collectors.toList());
		final List<Trace<S, A>> traces = arg.getCexs().map(ArgTrace::toTrace).collect(Collectors.toList());
		assert traces.size() == cexs.size();

		logger.write(Level.INFO, "|  |  Number of traces: %d%n", traces.size());
		assert traces.size() > 0 : "No counterexample in ARG";

		logger.write(Level.SUBSTEP, "|  |  Checking traces...");
		final List<ExprTraceStatus<R>> cexStatuses = new ArrayList<>(traces.size());
		for (final Trace<S, A> trace : traces) {
			final ExprTraceStatus<R> status = exprTraceChecker.check(trace);
			cexStatuses.add(status);
			if (status.isFeasible()) {
				break;
			}
		}

		if (cexStatuses.stream().anyMatch(ExprTraceStatus::isFeasible)) {
			logger.write(Level.SUBSTEP, "done, result: found feasible%n");
			return RefinerResult.unsafe(traces.get(
					cexStatuses.indexOf(cexStatuses.stream().filter(ExprTraceStatus::isFeasible).findFirst().get())));
		} else {
			assert cexStatuses.size() == cexs.size();
			logger.write(Level.SUBSTEP, "done, result: all infeasible%n");
			final List<R> refutations = cexStatuses.stream().map(s -> s.asInfeasible().getRefutation())
					.collect(Collectors.toList());
			assert refutations.size() == cexs.size();

			final List<ArgNode<S, A>> nodesToPrune = new ArrayList<>(traces.size());
			final List<Boolean> skip = new ArrayList<>(traces.size());
			for (int i = 0; i < traces.size(); ++i) {
				nodesToPrune.add(cexs.get(i).node(refutations.get(i).getPruneIndex()));
				skip.add(false);
			}
			assert nodesToPrune.size() == cexs.size();
			assert skip.size() == cexs.size();

			for (int i = 0; i < nodesToPrune.size(); ++i) {
				final ArgNode<S, A> node = nodesToPrune.get(i);
				if (node.properAncestors().anyMatch(a -> nodesToPrune.contains(a))) {
					skip.set(i, true);
				}
			}

			assert skip.stream().anyMatch(b -> b.equals(false));

			P refinedPrec = prec;
			for (int i = 0; i < refutations.size(); ++i) {
				if (!skip.get(i)) {
					refinedPrec = precRefiner.refine(refinedPrec, traces.get(i), refutations.get(i));
				}
			}
			switch (pruneStrategy){
				case LAZY:
					logger.write(Level.SUBSTEP, "|  |  Pruning (lazy)...");
					for (int i = 0; i < nodesToPrune.size(); ++i) {
						if (!skip.get(i)) {
							arg.prune(nodesToPrune.get(i));
						}
					}
					break;
				case FULL:
					logger.write(Level.SUBSTEP, "|  |  Pruning (full)...");
					arg.pruneAll();
					break;
				default:
					throw new UnsupportedOperationException("Unsupported pruning strategy");
			}
			logger.write(Level.SUBSTEP, "done%n");
			return RefinerResult.spurious(refinedPrec);
		}

	}

}