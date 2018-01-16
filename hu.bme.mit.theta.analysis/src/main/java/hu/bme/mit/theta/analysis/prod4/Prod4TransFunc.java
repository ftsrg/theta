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
package hu.bme.mit.theta.analysis.prod4;

import static com.google.common.base.Preconditions.checkNotNull;
import static java.util.Collections.singleton;

import java.util.Collection;
import java.util.Optional;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.TransFunc;

final class Prod4TransFunc<S1 extends State, S2 extends State, S3 extends State, S4 extends State, A extends Action, P1 extends Prec, P2 extends Prec, P3 extends Prec, P4 extends Prec>
		implements TransFunc<Prod4State<S1, S2, S3, S4>, A, Prod4Prec<P1, P2, P3, P4>> {

	private final TransFunc<S1, ? super A, P1> transFunc1;
	private final TransFunc<S2, ? super A, P2> transFunc2;
	private final TransFunc<S3, ? super A, P3> transFunc3;
	private final TransFunc<S4, ? super A, P4> transFunc4;

	private Prod4TransFunc(final TransFunc<S1, ? super A, P1> transFunc1, final TransFunc<S2, ? super A, P2> transFunc2,
			final TransFunc<S3, ? super A, P3> transFunc3, final TransFunc<S4, ? super A, P4> transFunc4) {
		this.transFunc1 = checkNotNull(transFunc1);
		this.transFunc2 = checkNotNull(transFunc2);
		this.transFunc3 = checkNotNull(transFunc3);
		this.transFunc4 = checkNotNull(transFunc4);
	}

	public static <S1 extends State, S2 extends State, S3 extends State, S4 extends State, A extends Action, P1 extends Prec, P2 extends Prec, P3 extends Prec, P4 extends Prec> Prod4TransFunc<S1, S2, S3, S4, A, P1, P2, P3, P4> create(
			final TransFunc<S1, ? super A, P1> transFunc1, final TransFunc<S2, ? super A, P2> transFunc2,
			final TransFunc<S3, ? super A, P3> transFunc3, final TransFunc<S4, ? super A, P4> transFunc4) {
		return new Prod4TransFunc<>(transFunc1, transFunc2, transFunc3, transFunc4);
	}

	@Override
	public Collection<Prod4State<S1, S2, S3, S4>> getSuccStates(final Prod4State<S1, S2, S3, S4> state, final A action,
			final Prod4Prec<P1, P2, P3, P4> prec) {
		checkNotNull(state);
		checkNotNull(action);
		checkNotNull(prec);

		if (state.isBottom()) {
			return singleton(state);
		}

		final Collection<? extends S1> succStates1 = transFunc1.getSuccStates(state.getState1(), action,
				prec.getPrec1());
		final Optional<? extends S1> optBottom1 = succStates1.stream().filter(State::isBottom).findAny();

		if (optBottom1.isPresent()) {
			final S1 bottom1 = optBottom1.get();
			return singleton(Prod4State.bottom1(bottom1));
		}

		final Collection<? extends S2> succStates2 = transFunc2.getSuccStates(state.getState2(), action,
				prec.getPrec2());
		final Optional<? extends S2> optBottom2 = succStates2.stream().filter(State::isBottom).findAny();

		if (optBottom2.isPresent()) {
			final S2 bottom2 = optBottom2.get();
			return singleton(Prod4State.bottom2(bottom2));
		}

		final Collection<? extends S3> succStates3 = transFunc3.getSuccStates(state.getState3(), action,
				prec.getPrec3());
		final Optional<? extends S3> optBottom3 = succStates3.stream().filter(State::isBottom).findAny();

		if (optBottom3.isPresent()) {
			final S3 bottom3 = optBottom3.get();
			return singleton(Prod4State.bottom3(bottom3));
		}

		final Collection<? extends S4> succStates4 = transFunc4.getSuccStates(state.getState4(), action,
				prec.getPrec4());
		final Optional<? extends S4> optBottom4 = succStates4.stream().filter(State::isBottom).findAny();

		if (optBottom4.isPresent()) {
			final S4 bottom4 = optBottom4.get();
			return singleton(Prod4State.bottom4(bottom4));
		}

		return Prod4State.cartesian(succStates1, succStates2, succStates3, succStates4);
	}

}
