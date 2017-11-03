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

import com.google.common.collect.ImmutableCollection;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;

import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.common.product.Product2;

public final class Prod2State<S1 extends State, S2 extends State> extends ProdState implements Product2<S1, S2> {

	private Prod2State(final S1 state1, final S2 state2) {
		super(ImmutableList.of(state1, state2));
	}

	public static <S1 extends State, S2 extends State> Prod2State<S1, S2> of(final S1 state1, final S2 state2) {
		return new Prod2State<>(state1, state2);
	}

	public static <S1 extends State, S2 extends State> Collection<Prod2State<S1, S2>> product(
			final Collection<? extends S1> states1, final Collection<? extends S2> states2) {
		checkNotNull(states1);
		checkNotNull(states2);

		final ImmutableCollection.Builder<Prod2State<S1, S2>> builder = ImmutableSet.builder();
		for (final S1 state1 : states1) {
			for (final S2 state2 : states2) {
				builder.add(Prod2State.of(state1, state2));
			}
		}
		return builder.build();
	}

	@Override
	public S1 _1() {
		@SuppressWarnings("unchecked")
		final S1 result = (S1) elem(0);
		return result;
	}

	@Override
	public S2 _2() {
		@SuppressWarnings("unchecked")
		final S2 result = (S2) elem(1);
		return result;
	}

	public <S extends State> Prod2State<S, S2> with1(final S state) {
		return Prod2State.of(state, _2());
	}

	public <S extends State> Prod2State<S1, S> with2(final S state) {
		return Prod2State.of(_1(), state);
	}

}
