/*
 *  Copyright 2022 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.analysis.expr;

import com.google.common.collect.Streams;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;

public final class BasicStackableExprState<S extends ExprState> implements StackableExprState<S> {
	private final List<S> states;

	private BasicStackableExprState(final List<S> states) {
		this.states = Collections.unmodifiableList(states);
	}

	public static <S extends ExprState> BasicStackableExprState<S> of(final List<S> states) {
		return new BasicStackableExprState<S>(states);
	}

	@Override
	public boolean isBottom() {
		return states.stream().anyMatch(State::isBottom);
	}

	@Override
	public Expr<BoolType> toExpr() {
		return And(states.stream().map(ExprState::toExpr).collect(Collectors.toSet()));
	}

	@Override
	public BasicStackableExprState<S> push(S s) {
		return BasicStackableExprState.of(Streams.concat(states.stream(), Stream.of(s)).collect(Collectors.toList()));
	}

	@Override
	public BasicStackableExprState<S> pop() {
		return BasicStackableExprState.of(states.stream().limit(states.size() - 1).collect(Collectors.toList()));
	}

	@Override
	public S peek() {
		return states.get(states.size() - 1);
	}

	@Override
	public List<S> getStates() {
		return states;
	}

	@Override
	public String toString() {
		return Utils.lispStringBuilder(getClass().getSimpleName()).body().addAll(states).toString();
	}
}
