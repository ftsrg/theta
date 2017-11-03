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
import hu.bme.mit.theta.common.product.Product3;

public final class Prod3State<S1 extends State, S2 extends State, S3 extends State> extends ProdState
		implements Product3<S1, S2, S3> {

	private Prod3State(final S1 state1, final S2 state2, final S3 state3) {
		super(ImmutableList.of(state1, state2, state3));
	}

	public static <S1 extends State, S2 extends State, S3 extends State> Prod3State<S1, S2, S3> of(final S1 state1,
			final S2 state2, final S3 state3) {
		return new Prod3State<>(state1, state2, state3);
	}

	public static <S1 extends State, S2 extends State, S3 extends State> Collection<Prod3State<S1, S2, S3>> product(
			final Collection<? extends S1> states1, final Collection<? extends S2> states2,
			final Collection<? extends S3> states3) {
		checkNotNull(states1);
		checkNotNull(states2);

		final ImmutableCollection.Builder<Prod3State<S1, S2, S3>> builder = ImmutableSet.builder();
		for (final S1 state1 : states1) {
			for (final S2 state2 : states2) {
				for (final S3 state3 : states3) {
					builder.add(Prod3State.of(state1, state2, state3));
				}
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

	@Override
	public S3 _3() {
		@SuppressWarnings("unchecked")
		final S3 result = (S3) elem(2);
		return result;
	}

	public <S extends State> Prod3State<S, S2, S3> with1(final S state) {
		return Prod3State.of(state, _2(), _3());
	}

	public <S extends State> Prod3State<S1, S, S3> with2(final S state) {
		return Prod3State.of(_1(), state, _3());
	}

	public <S extends State> Prod3State<S1, S2, S> with3(final S state) {
		return Prod3State.of(_1(), _2(), state);
	}

}
