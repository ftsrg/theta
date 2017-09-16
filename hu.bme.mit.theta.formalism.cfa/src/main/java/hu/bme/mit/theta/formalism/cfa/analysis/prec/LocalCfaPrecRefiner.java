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
package hu.bme.mit.theta.formalism.cfa.analysis.prec;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.HashMap;
import java.util.Map;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.refinement.PrecRefiner;
import hu.bme.mit.theta.analysis.expr.refinement.Refutation;
import hu.bme.mit.theta.analysis.expr.refinement.RefutationToPrec;
import hu.bme.mit.theta.formalism.cfa.CFA.Loc;
import hu.bme.mit.theta.formalism.cfa.analysis.CfaPrec;
import hu.bme.mit.theta.formalism.cfa.analysis.CfaState;

public final class LocalCfaPrecRefiner<S extends ExprState, A extends Action, P extends Prec, R extends Refutation>
		implements PrecRefiner<CfaState<S>, A, CfaPrec<P>, R> {

	private final RefutationToPrec<P, R> refToPrec;

	private LocalCfaPrecRefiner(final RefutationToPrec<P, R> refToPrec) {
		this.refToPrec = checkNotNull(refToPrec);
	}

	public static <S extends ExprState, A extends Action, P extends Prec, R extends Refutation> LocalCfaPrecRefiner<S, A, P, R> create(
			final RefutationToPrec<P, R> refToPrec) {
		return new LocalCfaPrecRefiner<>(refToPrec);
	}

	@Override
	public CfaPrec<P> refine(final CfaPrec<P> prec, final Trace<CfaState<S>, A> trace, final R refutation) {
		checkNotNull(trace);
		checkNotNull(prec);
		checkNotNull(refutation);
		checkArgument(prec instanceof LocalCfaPrec); // TODO: enforce this in a
														// better way

		// Important: the same location may appear multiple times in the trace
		// and in this case the corresponding precisions should be joined before
		// joining them to the old precision of the location

		final LocalCfaPrec<P> genPrec = (LocalCfaPrec<P>) prec;
		final Map<Loc, P> runningPrecs = new HashMap<>();
		for (final CfaState<S> state : trace.getStates()) {
			runningPrecs.put(state.getLoc(), genPrec.getPrec(state.getLoc()));
		}

		for (int i = 0; i < trace.getStates().size(); ++i) {
			final Loc loc = trace.getState(i).getLoc();
			final P precForLoc = runningPrecs.get(loc);
			final P newPrecForLoc = refToPrec.toPrec(refutation, i);
			runningPrecs.put(loc, refToPrec.join(precForLoc, newPrecForLoc));
		}

		return genPrec.refine(runningPrecs);
	}

	@Override
	public String toString() {
		return getClass().getSimpleName();
	}
}
