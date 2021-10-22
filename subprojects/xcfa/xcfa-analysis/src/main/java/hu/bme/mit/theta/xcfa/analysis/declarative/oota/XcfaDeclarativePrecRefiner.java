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
package hu.bme.mit.theta.xcfa.analysis.declarative.oota;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.refinement.PrecRefiner;
import hu.bme.mit.theta.analysis.expr.refinement.Refutation;
import hu.bme.mit.theta.analysis.expr.refinement.RefutationToPrec;
import hu.bme.mit.theta.core.decl.VarDecl;

import java.util.Set;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkNotNull;

public final class XcfaDeclarativePrecRefiner<S extends ExprState, A extends Action, P extends Prec, R extends Refutation>
		implements PrecRefiner<XcfaDeclarativeState<S>, A, XcfaDeclarativePrec<P>, R> {

	private final RefutationToPrec<P, R> refToPrec;
	private final Set<VarDecl<?>> globalVars;

	private XcfaDeclarativePrecRefiner(final RefutationToPrec<P, R> refToPrec, final Set<VarDecl<?>> globalVars) {
		this.refToPrec = checkNotNull(refToPrec);
		this.globalVars = globalVars;
	}

	public static <S extends ExprState, A extends Action, P extends Prec, R extends Refutation> XcfaDeclarativePrecRefiner<S, A, P, R> create(
			final Set<VarDecl<?>> globalVars,
			final RefutationToPrec<P, R> refToPrec) {
		return new XcfaDeclarativePrecRefiner<>(refToPrec, globalVars);
	}

	@Override
	public XcfaDeclarativePrec<P> refine(final XcfaDeclarativePrec<P> prec, final Trace<XcfaDeclarativeState<S>, A> trace, final R refutation) {
		checkNotNull(trace);
		checkNotNull(prec);
		checkNotNull(refutation);
		P runningPrec = prec.getGlobalPrec();
		for (int i = 0; i < trace.getStates().size(); ++i) {
			final P precFromRef = refToPrec.toPrec(refutation, i);
			runningPrec = refToPrec.join(runningPrec, precFromRef);
		}
		final Set<VarDecl<?>> usedGlobalVars = runningPrec.getUsedVars().stream().filter(this.globalVars::contains).collect(Collectors.toSet());
		return prec.refine(runningPrec, usedGlobalVars);
	}

	@Override
	public String toString() {
		return getClass().getSimpleName();
	}

}
