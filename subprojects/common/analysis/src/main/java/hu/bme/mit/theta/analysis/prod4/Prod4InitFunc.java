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

import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;

final class Prod4InitFunc<S1 extends State, S2 extends State, S3 extends State, S4 extends State, P1 extends Prec, P2 extends Prec, P3 extends Prec, P4 extends Prec>
		implements InitFunc<Prod4State<S1, S2, S3, S4>, Prod4Prec<P1, P2, P3, P4>> {

	private final InitFunc<S1, P1> initFunc1;
	private final InitFunc<S2, P2> initFunc2;
	private final InitFunc<S3, P3> initFunc3;
	private final InitFunc<S4, P4> initFunc4;

	private Prod4InitFunc(final InitFunc<S1, P1> initFunc1, final InitFunc<S2, P2> initFunc2,
						  final InitFunc<S3, P3> initFunc3, final InitFunc<S4, P4> initFunc4) {
		this.initFunc1 = checkNotNull(initFunc1);
		this.initFunc2 = checkNotNull(initFunc2);
		this.initFunc3 = checkNotNull(initFunc3);
		this.initFunc4 = checkNotNull(initFunc4);
	}

	public static <S1 extends State, S2 extends State, S3 extends State, S4 extends State, P1 extends Prec, P2 extends Prec, P3 extends Prec, P4 extends Prec> Prod4InitFunc<S1, S2, S3, S4, P1, P2, P3, P4> create(
			final InitFunc<S1, P1> initFunc1, final InitFunc<S2, P2> initFunc2, final InitFunc<S3, P3> initFunc3,
			final InitFunc<S4, P4> initFunc4) {
		return new Prod4InitFunc<>(initFunc1, initFunc2, initFunc3, initFunc4);
	}

	@Override
	public Collection<Prod4State<S1, S2, S3, S4>> getInitStates(final Prod4Prec<P1, P2, P3, P4> prec) {
		checkNotNull(prec);
		final Collection<? extends S1> initStates1 = initFunc1.getInitStates(prec.getPrec1());
		final Optional<? extends S1> optBottom1 = initStates1.stream().filter(State::isBottom).findAny();

		if (optBottom1.isPresent()) {
			final S1 bottom1 = optBottom1.get();
			return singleton(Prod4State.bottom1(bottom1));
		}

		final Collection<? extends S2> initStates2 = initFunc2.getInitStates(prec.getPrec2());
		final Optional<? extends S2> optBottom2 = initStates2.stream().filter(State::isBottom).findAny();

		if (optBottom2.isPresent()) {
			final S2 bottom2 = optBottom2.get();
			return singleton(Prod4State.bottom2(bottom2));
		}

		final Collection<? extends S3> initStates3 = initFunc3.getInitStates(prec.getPrec3());
		final Optional<? extends S3> optBottom3 = initStates3.stream().filter(State::isBottom).findAny();

		if (optBottom3.isPresent()) {
			final S3 bottom3 = optBottom3.get();
			return singleton(Prod4State.bottom3(bottom3));
		}

		final Collection<? extends S4> initStates4 = initFunc4.getInitStates(prec.getPrec4());
		final Optional<? extends S4> optBottom4 = initStates4.stream().filter(State::isBottom).findAny();

		if (optBottom4.isPresent()) {
			final S4 bottom4 = optBottom4.get();
			return singleton(Prod4State.bottom4(bottom4));
		}

		return Prod4State.cartesian(initStates1, initStates2, initStates3, initStates4);
	}

}
