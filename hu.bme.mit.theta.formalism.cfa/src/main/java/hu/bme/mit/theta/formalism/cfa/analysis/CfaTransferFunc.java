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
package hu.bme.mit.theta.formalism.cfa.analysis;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.TransferFunc;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.formalism.cfa.CFA.Edge;
import hu.bme.mit.theta.formalism.cfa.CFA.Loc;

final class CfaTransferFunc<S extends ExprState, P extends Prec>
		implements TransferFunc<CfaState<S>, CfaAction, CfaPrec<P>> {

	private final TransferFunc<S, ? super CfaAction, ? super P> transferFunc;

	private CfaTransferFunc(final TransferFunc<S, ? super CfaAction, ? super P> transferFunc) {
		this.transferFunc = checkNotNull(transferFunc);
	}

	public static <S extends ExprState, P extends Prec> CfaTransferFunc<S, P> create(
			final TransferFunc<S, ? super CfaAction, ? super P> transferFunc) {
		return new CfaTransferFunc<>(transferFunc);
	}

	@Override
	public Collection<CfaState<S>> getSuccStates(final CfaState<S> state, final CfaAction action,
			final CfaPrec<P> prec) {
		checkNotNull(state);
		checkNotNull(action);
		checkNotNull(prec);

		final Edge edge = action.getEdge();
		final Loc source = edge.getSource();
		final Loc target = edge.getTarget();
		checkArgument(state.getLoc().equals(source), "Location mismatch");

		final Collection<CfaState<S>> succStates = new ArrayList<>();

		final P subPrec = prec.getPrec(target);
		final S subState = state.getState();

		final Collection<? extends S> subSuccStates = transferFunc.getSuccStates(subState, action, subPrec);
		for (final S subSuccState : subSuccStates) {
			final CfaState<S> succState = CfaState.of(target, subSuccState);
			succStates.add(succState);
		}
		return succStates;
	}

}
