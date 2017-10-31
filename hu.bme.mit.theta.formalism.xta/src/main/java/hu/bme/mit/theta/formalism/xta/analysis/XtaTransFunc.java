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
package hu.bme.mit.theta.formalism.xta.analysis;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.List;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.formalism.xta.XtaProcess.Loc;

final class XtaTransFunc<S extends State, P extends Prec> implements TransFunc<XtaState<S>, XtaAction, P> {

	private final TransFunc<S, ? super XtaAction, ? super P> transFunc;

	private XtaTransFunc(final TransFunc<S, ? super XtaAction, ? super P> transFunc) {
		this.transFunc = checkNotNull(transFunc);
	}

	public static <S extends State, P extends Prec> XtaTransFunc<S, P> create(
			final TransFunc<S, ? super XtaAction, ? super P> transferFunc) {
		return new XtaTransFunc<>(transferFunc);
	}

	@Override
	public Collection<XtaState<S>> getSuccStates(final XtaState<S> state, final XtaAction action, final P prec) {
		checkNotNull(state);
		checkNotNull(action);
		checkNotNull(prec);
		checkArgument(state.getLocs().equals(action.getSourceLocs()));
		final List<Loc> succLocs = action.getTargetLocs();
		final S subState = state.getState();
		final Collection<? extends S> succSubStates = transFunc.getSuccStates(subState, action, prec);
		return XtaState.collectionOf(succLocs, succSubStates);
	}

}
