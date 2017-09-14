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

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.common.product.Product2;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

public final class Prod2State<S1 extends State, S2 extends State> extends ProdState implements Product2<S1, S2> {

	Prod2State(final S1 state1, final S2 state2) {
		super(ImmutableList.of(state1, state2));
	}

	////

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

	////

	public <S extends State> Prod2State<S, S2> with1(final S state) {
		return ProdState.of(state, _2());
	}

	public <S extends State> Prod2State<S1, S> with2(final S state) {
		return ProdState.of(_1(), state);
	}

	////

	@Override
	public Expr<BoolType> toExpr() {
		if (_1() instanceof ExprState && _2() instanceof ExprState) {
			final ExprState exprState1 = (ExprState) _1();
			final ExprState exprState2 = (ExprState) _2();
			return And(exprState1.toExpr(), exprState2.toExpr());
		} else {
			throw new UnsupportedOperationException();
		}
	}

}
