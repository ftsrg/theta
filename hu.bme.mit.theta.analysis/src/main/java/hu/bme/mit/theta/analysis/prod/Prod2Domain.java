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

import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.State;

final class Prod2Domain<S1 extends State, S2 extends State> implements Domain<Prod2State<S1, S2>> {

	private final Domain<S1> domain1;
	private final Domain<S2> domain2;

	private Prod2Domain(final Domain<S1> domain1, final Domain<S2> domain2) {
		this.domain1 = checkNotNull(domain1);
		this.domain2 = checkNotNull(domain2);
	}

	public static <S1 extends State, S2 extends State> Prod2Domain<S1, S2> create(final Domain<S1> domain1,
			final Domain<S2> domain2) {
		return new Prod2Domain<>(domain1, domain2);
	}

	@Override
	public boolean isLeq(final Prod2State<S1, S2> state1, final Prod2State<S1, S2> state2) {
		return domain1.isLeq(state1._1(), state2._1()) && domain2.isLeq(state1._2(), state2._2());
	}

}
