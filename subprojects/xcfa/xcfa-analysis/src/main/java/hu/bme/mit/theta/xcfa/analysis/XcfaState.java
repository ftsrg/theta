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
package hu.bme.mit.theta.xcfa.analysis;

import com.google.common.collect.Streams;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

import java.util.Collection;
import java.util.Map;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;

public final class XcfaState<S extends ExprState> implements ExprState {
	private final Map<Integer, XcfaProcessState<S>> processStates;
	private final Collection<Integer> enabledProcesses;
	private final S globalState;

	private XcfaState(final Map<Integer, XcfaProcessState<S>> processStates, final Collection<Integer> enabledProcesses, final S globalState) {
		this.processStates = checkNotNull(processStates);
		this.enabledProcesses = checkNotNull(enabledProcesses);
		this.globalState = checkNotNull(globalState);
	}

	public static <S extends ExprState> XcfaState<S> create(final Map<Integer, XcfaProcessState<S>> processStates, final Collection<Integer> enabledProcesses, final S globalState) {
		return new XcfaState<>(processStates, enabledProcesses, globalState);
	}

	@Override
	public boolean isBottom() {
		return enabledProcesses.size() == 0 || globalState.isBottom() || processStates.values().stream().anyMatch(XcfaProcessState::isBottom);
	}

	@Override
	public Expr<BoolType> toExpr() {
		return And(Streams.concat(processStates.values().stream().map(XcfaProcessState::toExpr), Stream.of(globalState.toExpr())).collect(Collectors.toList()));
	}

	public Collection<Integer> getEnabledProcesses() {
		return enabledProcesses;
	}
}
