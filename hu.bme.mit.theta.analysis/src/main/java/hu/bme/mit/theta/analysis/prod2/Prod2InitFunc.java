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

import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;

final class Prod2InitFunc<S1 extends State, S2 extends State, P1 extends Prec, P2 extends Prec>
		implements InitFunc<Prod2State<S1, S2>, Prod2Prec<P1, P2>> {

	private final InitFunc<S1, P1> initFunc1;
	private final InitFunc<S2, P2> initFunc2;

	private Prod2InitFunc(final InitFunc<S1, P1> initFunc1, final InitFunc<S2, P2> initFunc2) {
		this.initFunc1 = checkNotNull(initFunc1);
		this.initFunc2 = checkNotNull(initFunc2);
	}

	public static <S1 extends State, S2 extends State, P1 extends Prec, P2 extends Prec> Prod2InitFunc<S1, S2, P1, P2> create(
			final InitFunc<S1, P1> initFunc1, final InitFunc<S2, P2> initFunc2) {
		return new Prod2InitFunc<>(initFunc1, initFunc2);
	}

	@Override
	public Collection<? extends Prod2State<S1, S2>> getInitStates(final Prod2Prec<P1, P2> prec) {
		checkNotNull(prec);
		final Collection<? extends S1> initStates1 = initFunc1.getInitStates(prec._1());
		final Optional<? extends S1> optBottom1 = initStates1.stream().filter(State::isBottom).findAny();

		if (optBottom1.isPresent()) {
			final S1 bottom1 = optBottom1.get();
			return singleton(Prod2State.bottom1(bottom1));
		}

		final Collection<? extends S2> initStates2 = initFunc2.getInitStates(prec._2());
		final Optional<? extends S2> optBottom2 = initStates2.stream().filter(State::isBottom).findAny();

		if (optBottom2.isPresent()) {
			final S2 bottom2 = optBottom2.get();
			return singleton(Prod2State.bottom2(bottom2));
		}

		return Prod2State.cartesian(initStates1, initStates2);
	}

}
