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
package hu.bme.mit.theta.formalism.xta.analysis;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.State;

final class XtaDomain<S extends State> implements Domain<XtaState<S>> {

	private final Domain<S> domain;

	private XtaDomain(final Domain<S> domain) {
		this.domain = checkNotNull(domain);
	}

	public static <S extends State> XtaDomain<S> create(final Domain<S> domain) {
		return new XtaDomain<>(domain);
	}

	@Override
	public boolean isTop(final XtaState<S> state) {
		checkNotNull(state);
		return false;
	}

	@Override
	public boolean isBottom(final XtaState<S> state) {
		checkNotNull(state);
		return domain.isBottom(state.getState());
	}

	@Override
	public boolean isLeq(final XtaState<S> state1, final XtaState<S> state2) {
		checkNotNull(state1);
		checkNotNull(state2);
		return state1.getLocs().equals(state2.getLocs()) && domain.isLeq(state1.getState(), state2.getState());
	}

}
