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

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.common.product.Product3;

public final class Prod3State<S1 extends State, S2 extends State, S3 extends State> extends ProdState
		implements Product3<S1, S2, S3> {

	Prod3State(final S1 state1, final S2 state2, final S3 state3) {
		super(ImmutableList.of(state1, state2, state3));
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
		return ProdState.of(state, _2(), _3());
	}

	public <S extends State> Prod3State<S1, S, S3> with2(final S state) {
		return ProdState.of(_1(), state, _3());
	}

	public <S extends State> Prod3State<S1, S2, S> with3(final S state) {
		return ProdState.of(_1(), _2(), state);
	}

}
