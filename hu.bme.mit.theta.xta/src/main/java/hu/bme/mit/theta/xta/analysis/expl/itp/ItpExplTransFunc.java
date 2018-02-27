/*
 *  Copyright 2018 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.xta.analysis.expl.itp;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.analysis.expl.ExplState;

final class ItpExplTransFunc<A extends Action> implements TransFunc<ItpExplState, A, ExplPrec> {

	private final TransFunc<ExplState, ? super A, ExplPrec> transFunc;

	public ItpExplTransFunc(final TransFunc<ExplState, ? super A, ExplPrec> transFunc) {
		this.transFunc = checkNotNull(transFunc);
	}

	public static final <A extends Action> ItpExplTransFunc<A> create(
			final TransFunc<ExplState, ? super A, ExplPrec> transFunc) {
		return new ItpExplTransFunc<>(transFunc);
	}

	@Override
	public Collection<ItpExplState> getSuccStates(final ItpExplState state, final A action, final ExplPrec prec) {
		checkNotNull(state);
		checkNotNull(action);
		checkNotNull(prec);

		final ExplState subState = state.getConcrState();
		final Collection<? extends ExplState> subSuccStates = transFunc.getSuccStates(subState, action, prec);

		if (subSuccStates.isEmpty()) {
			final ItpExplState succState = ItpExplState.of(ExplState.bottom(), ExplState.top());
			return Collections.singleton(succState);
		} else {
			final Collection<ItpExplState> result = new ArrayList<>(subSuccStates.size());
			for (final ExplState subSuccState : subSuccStates) {
				final ItpExplState succState = ItpExplState.of(subSuccState, ExplState.top());
				result.add(succState);
			}
			return result;
		}
	}

}
