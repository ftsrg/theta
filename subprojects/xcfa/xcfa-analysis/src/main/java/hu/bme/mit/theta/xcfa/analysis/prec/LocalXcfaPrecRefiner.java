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
package hu.bme.mit.theta.xcfa.analysis.prec;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.MultiStackableExprState;
import hu.bme.mit.theta.analysis.expr.StackableExprState;
import hu.bme.mit.theta.analysis.expr.refinement.PrecRefiner;
import hu.bme.mit.theta.analysis.expr.refinement.Refutation;
import hu.bme.mit.theta.analysis.expr.refinement.RefutationToPrec;
import hu.bme.mit.theta.common.container.Containers;
import hu.bme.mit.theta.xcfa.analysis.XcfaLocationState;
import hu.bme.mit.theta.xcfa.analysis.XcfaPrec;
import hu.bme.mit.theta.xcfa.analysis.XcfaState;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;

import java.util.Map;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

public final class LocalXcfaPrecRefiner<S extends ExprState, SS extends StackableExprState<XcfaLocationState<S>>, SSS extends MultiStackableExprState<Integer, XcfaLocationState<S>, SS>, A extends Action, P extends Prec, R extends Refutation>
		implements PrecRefiner<XcfaState<S, SS, SSS>, A, XcfaPrec<P>, R> {

	private final RefutationToPrec<P, R> refToPrec;

	private LocalXcfaPrecRefiner(final RefutationToPrec<P, R> refToPrec) {
		this.refToPrec = checkNotNull(refToPrec);
	}

	public static <S extends ExprState, SS extends StackableExprState<XcfaLocationState<S>>, SSS extends MultiStackableExprState<Integer, XcfaLocationState<S>, SS>, A extends Action, P extends Prec, R extends Refutation> LocalXcfaPrecRefiner<S, SS, SSS, A, P, R> create(
			final RefutationToPrec<P, R> refToPrec) {
		return new LocalXcfaPrecRefiner<>(refToPrec);
	}

	@Override
	public XcfaPrec<P> refine(final XcfaPrec<P> prec, final Trace<XcfaState<S, SS, SSS>, A> trace, final R refutation) {
		checkNotNull(trace);
		checkNotNull(prec);
		checkNotNull(refutation);
		checkArgument(prec instanceof LocalXcfaPrec); // TODO: enforce this in a
		// better way

		// Important: the same location may appear multiple times in the trace
		// and in this case the corresponding precisions should be joined before
		// joining them to the old precision of the location

		final LocalXcfaPrec<P> genPrec = (LocalXcfaPrec<P>) prec;
		final Map<XcfaLocation, P> runningPrecs = Containers.createMap();
		for (final XcfaState<S, SS, SSS> state : trace.getStates()) {
			for (Map.Entry<Integer, XcfaLocation> xcfaLocationEntry : state.getLocations().entrySet()) {
				runningPrecs.put(xcfaLocationEntry.getValue(), genPrec.getPrec(xcfaLocationEntry.getValue()));
			}
		}

		for (int i = 0; i < trace.getStates().size(); ++i) {
			for (Map.Entry<Integer, XcfaLocation> xcfaLocationEntry : trace.getState(i).getLocations().entrySet()) {
				final XcfaLocation loc = xcfaLocationEntry.getValue();
				final P precForLoc = runningPrecs.get(loc);
				final P newPrecForLoc = refToPrec.toPrec(refutation, i);
				runningPrecs.put(loc, refToPrec.join(precForLoc, newPrecForLoc));
			}
		}

		return genPrec.refine(runningPrecs);
	}

	@Override
	public String toString() {
		return getClass().getSimpleName();
	}
}
