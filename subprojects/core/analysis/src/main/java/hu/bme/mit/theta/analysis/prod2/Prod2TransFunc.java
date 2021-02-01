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
package hu.bme.mit.theta.analysis.prod2;

import static com.google.common.base.Preconditions.checkNotNull;
import static java.util.Collections.singleton;

import java.util.Collection;
import java.util.Optional;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.TransFunc;

final class Prod2TransFunc<S1 extends State, S2 extends State, A extends Action, P1 extends Prec, P2 extends Prec>
		implements TransFunc<Prod2State<S1, S2>, A, Prod2Prec<P1, P2>> {

	private final TransFunc<S1, ? super A, P1> transFunc1;
	private final TransFunc<S2, ? super A, P2> transFunc2;
	private final PreStrengtheningOperator<S1, S2> preStrenghteningOperator;
	private final StrengtheningOperator<S1, S2, P1, P2> strenghteningOperator;

	private Prod2TransFunc(final TransFunc<S1, ? super A, P1> transFunc1, final TransFunc<S2, ? super A, P2> transFunc2,
						   final PreStrengtheningOperator<S1, S2> preStrengtheningOperator,
						   final StrengtheningOperator<S1, S2, P1, P2> strenghteningOperator) {
		this.transFunc1 = checkNotNull(transFunc1);
		this.transFunc2 = checkNotNull(transFunc2);
		this.strenghteningOperator = checkNotNull(strenghteningOperator);
		this.preStrenghteningOperator = checkNotNull(preStrengtheningOperator);
	}

	public static <S1 extends State, S2 extends State, A extends Action, P1 extends Prec, P2 extends Prec> Prod2TransFunc<S1, S2, A, P1, P2> create(
			final TransFunc<S1, ? super A, P1> transFunc1, final TransFunc<S2, ? super A, P2> transFunc2) {
		return create(transFunc1, transFunc2, DefaultPreStrengtheningOperator.create(), (states, prec) -> states);
	}

	public static <S1 extends State, S2 extends State, A extends Action, P1 extends Prec, P2 extends Prec> Prod2TransFunc<S1, S2, A, P1, P2> create(
			final TransFunc<S1, ? super A, P1> transFunc1, final TransFunc<S2, ? super A, P2> transFunc2,
			final PreStrengtheningOperator<S1, S2> preStrengtheningOperator,
			final StrengtheningOperator<S1, S2, P1, P2> strenghteningOperator
	) {
		return new Prod2TransFunc<>(transFunc1, transFunc2, preStrengtheningOperator, strenghteningOperator);
	}

	@Override
	public Collection<Prod2State<S1, S2>> getSuccStates(final Prod2State<S1, S2> state, final A action,
														final Prod2Prec<P1, P2> prec) {
		checkNotNull(state);
		checkNotNull(action);
		checkNotNull(prec);

		if (state.isBottom()) {
			return singleton(state);
		}

		final Collection<? extends S1> succStates1 = transFunc1.getSuccStates(preStrenghteningOperator.strengthenState1(state),
				action, prec.getPrec1());
		final Optional<? extends S1> optBottom1 = succStates1.stream().filter(State::isBottom).findAny();

		if (optBottom1.isPresent()) {
			final S1 bottom1 = optBottom1.get();
			return singleton(Prod2State.bottom1(bottom1));
		}

		final Collection<? extends S2> succStates2 = transFunc2.getSuccStates(preStrenghteningOperator.strengthenState2(state),
				action, prec.getPrec2());
		final Optional<? extends S2> optBottom2 = succStates2.stream().filter(State::isBottom).findAny();

		if (optBottom2.isPresent()) {
			final S2 bottom2 = optBottom2.get();
			return singleton(Prod2State.bottom2(bottom2));
		}

		final Collection<Prod2State<S1, S2>> succStates = Prod2State.cartesian(succStates1, succStates2);

		return strenghteningOperator.strengthen(succStates, prec);
	}

}
