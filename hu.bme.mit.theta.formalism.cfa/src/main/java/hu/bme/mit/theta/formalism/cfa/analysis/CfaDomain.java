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
package hu.bme.mit.theta.formalism.cfa.analysis;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.expr.ExprState;

public final class CfaDomain<S extends ExprState> implements Domain<CfaState<S>> {

	private final Domain<S> domain;

	private CfaDomain(final Domain<S> domain) {
		this.domain = checkNotNull(domain);
	}

	public static <S extends ExprState> CfaDomain<S> create(final Domain<S> domain) {
		return new CfaDomain<>(domain);
	}

	@Override
	public boolean isTop(final CfaState<S> state) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public boolean isBottom(final CfaState<S> state) {
		return domain.isBottom(state.getState());
	}

	@Override
	public boolean isLeq(final CfaState<S> state1, final CfaState<S> state2) {
		return state1.getLoc().equals(state2.getLoc()) && domain.isLeq(state1.getState(), state2.getState());
	}

}
