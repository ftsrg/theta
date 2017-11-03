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
package hu.bme.mit.theta.analysis.prod;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.TransFunc;

final class Prod2TransFunc<S1 extends State, S2 extends State, A extends Action, P1 extends Prec, P2 extends Prec>
		implements TransFunc<Prod2State<S1, S2>, A, Prod2Prec<P1, P2>> {

	private final TransFunc<S1, ? super A, P1> transFunc1;
	private final TransFunc<S2, ? super A, P2> transFunc2;

	private Prod2TransFunc(final TransFunc<S1, ? super A, P1> transFunc1,
			final TransFunc<S2, ? super A, P2> transFunc2) {
		this.transFunc1 = checkNotNull(transFunc1);
		this.transFunc2 = checkNotNull(transFunc2);
	}

	public static <S1 extends State, S2 extends State, A extends Action, P1 extends Prec, P2 extends Prec> Prod2TransFunc<S1, S2, A, P1, P2> create(
			final TransFunc<S1, ? super A, P1> transFunc1, final TransFunc<S2, ? super A, P2> transFunc2) {
		return new Prod2TransFunc<>(transFunc1, transFunc2);
	}

	@Override
	public Collection<? extends Prod2State<S1, S2>> getSuccStates(final Prod2State<S1, S2> state, final A action,
			final Prod2Prec<P1, P2> prec) {
		checkNotNull(state);
		checkNotNull(action);
		checkNotNull(prec);
		final Collection<? extends S1> succStates1 = transFunc1.getSuccStates(state._1(), action, prec._1());
		final Collection<? extends S2> succStates2 = transFunc2.getSuccStates(state._2(), action, prec._2());
		return Prod2State.product(succStates1, succStates2);
	}

}
