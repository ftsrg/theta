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

import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;

import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.Map;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

public final class XcfaState<S extends ExprState> implements ExprState {
	private final Map<Integer, XcfaLocation> processLocs;
	private final Collection<Integer> enabledProcesses;
	private final S globalState;

	private XcfaState(final Map<Integer, XcfaLocation> processLocs, final Collection<Integer> enabledProcesses, final S globalState) {
		this.processLocs = checkNotNull(processLocs);
		this.enabledProcesses = checkNotNull(enabledProcesses);
		this.globalState = checkNotNull(globalState);
	}

	public static <S extends ExprState> XcfaState<S> create(final Map<Integer, XcfaLocation> processLocs, final Collection<Integer> enabledProcesses, final S globalState) {
		return new XcfaState<>(processLocs, enabledProcesses, globalState);
	}

	@Override
	public boolean isBottom() {
		return enabledProcesses.size() == 0 || globalState.isBottom();
	}

	@Override
	public Expr<BoolType> toExpr() {
		return globalState.toExpr();
	}

	public Collection<Integer> getEnabledProcesses() {
		return enabledProcesses;
	}

	public Map<Integer, XcfaLocation> getProcessLocs() {
		return processLocs;
	}

	public S getGlobalState() {
		return globalState;
	}

	public XcfaState<S> advance(final S succState, final Integer process, final XcfaLocation target) {
		checkState(processLocs.containsKey(process));
		final Map<Integer, XcfaLocation> newProcessLocs = new LinkedHashMap<>(processLocs);
		newProcessLocs.put(process, target);
		return new XcfaState<>(newProcessLocs, enabledProcesses, succState);
	}

	public boolean isError() {
		return processLocs.values().stream().anyMatch(XcfaLocation::isErrorLoc);
	}
}
