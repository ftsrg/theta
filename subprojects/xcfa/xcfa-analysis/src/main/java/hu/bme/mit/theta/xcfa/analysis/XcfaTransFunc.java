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
package hu.bme.mit.theta.xcfa.analysis;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.MultiStackableExprState;
import hu.bme.mit.theta.analysis.expr.StackableExprState;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Map;

import static com.google.common.base.Preconditions.checkNotNull;

final class XcfaTransFunc<S extends ExprState, SS extends StackableExprState<XcfaLocationState<S>>, SSS extends MultiStackableExprState<Integer, XcfaLocationState<S>, SS>, P extends Prec>
		implements TransFunc<XcfaState<S, SS, SSS>, XcfaAction, XcfaPrec<P>> {

	private final TransFunc<S, ? super XcfaAction, ? super P> transFunc;

	private XcfaTransFunc(final TransFunc<S, ? super XcfaAction, ? super P> transFunc) {
		this.transFunc = checkNotNull(transFunc);
	}

	public static <S extends ExprState, SS extends StackableExprState<XcfaLocationState<S>>, SSS extends MultiStackableExprState<Integer, XcfaLocationState<S>, SS>, P extends Prec> XcfaTransFunc<S, SS, SSS, P> create(
			final TransFunc<S, ? super XcfaAction, ? super P> transFunc) {
		return new XcfaTransFunc<>(transFunc);
	}

	@Override
	public Collection<XcfaState<S, SS, SSS>> getSuccStates(final XcfaState<S, SS, SSS> state, final XcfaAction action,
												  final XcfaPrec<P> prec) {
		checkNotNull(state);
		checkNotNull(action);
		checkNotNull(prec);

		final XcfaLocation source = action.getSource();
		final XcfaLocation target = action.getTarget();

		for (Map.Entry<Integer, SS> entry : state.getState().getStates().entrySet()) {
			Integer key = entry.getKey();
			SS ss = entry.getValue();
			XcfaLocationState<S> peek = ss.peek();
			if(peek.getLoc() == source) {
				final Collection<XcfaState<S, SS, SSS>> succStates = new ArrayList<>();
				for (S succState : transFunc.getSuccStates(peek.getState(), action, prec.getPrec(source))) {
					//noinspection unchecked
					succStates.add(state.withState((SSS)state.getState().update(key, (SS) ss.pop().push(peek.withLoc(target).withState(succState)))));
				}
				return succStates;
			}
		}
		throw new RuntimeException("No such source location " + source);
	}

}
