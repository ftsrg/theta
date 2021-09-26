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
package hu.bme.mit.theta.xcfa.analysis.declarative;

import com.google.common.collect.ImmutableMap;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaProcess;

import java.util.List;
import java.util.Map;

import static com.google.common.base.Preconditions.checkNotNull;

public class XcfaDeclarativeState<S extends ExprState> implements ExprState {
	private final XcfaLocation currentLoc;
	private final Map<Integer, XcfaProcess> backlog;
	private final Map<VarDecl<?>, Integer> threadLookup;
	private final S globalState;
	private final Map<VarDecl<?>, List<XcfaLabel.LoadXcfaLabel<?>>> loads;
	private final Map<VarDecl<?>, List<XcfaLabel.StoreXcfaLabel<?>>> stores;

	private XcfaDeclarativeState(final XcfaLocation currentLoc, final Map<Integer, XcfaProcess> backlog, final Map<VarDecl<?>, Integer> threadLookup, final S globalState, final Map<VarDecl<?>, List<XcfaLabel.LoadXcfaLabel<?>>> loads, final Map<VarDecl<?>, List<XcfaLabel.StoreXcfaLabel<?>>> stores) {
		this.currentLoc = checkNotNull(currentLoc);
		this.backlog = ImmutableMap.copyOf(checkNotNull(backlog));
		this.threadLookup = ImmutableMap.copyOf(checkNotNull(threadLookup));
		this.globalState = checkNotNull(globalState);
		this.loads = ImmutableMap.copyOf(checkNotNull(loads));
		this.stores = ImmutableMap.copyOf(checkNotNull(stores));
	}

	public static <S extends ExprState> XcfaDeclarativeState<S> fromParams(final XcfaLocation currentLoc, final Map<Integer, XcfaProcess> backlog, final Map<VarDecl<?>, Integer> threadLookup, final S globalState, final Map<VarDecl<?>, List<XcfaLabel.LoadXcfaLabel<?>>> loads, final Map<VarDecl<?>, List<XcfaLabel.StoreXcfaLabel<?>>> stores) {
		return new XcfaDeclarativeState<S>(currentLoc, backlog, threadLookup, globalState, loads, stores);
	}

	public static <S extends ExprState> XcfaDeclarativeState<S> create(final XcfaLocation currentLoc, final S globalState) {
		return fromParams(currentLoc, Map.of(), Map.of(), globalState, Map.of(), Map.of());
	}

	@Override
	public boolean isBottom() {
		return globalState.isBottom();
	}

	@Override
	public Expr<BoolType> toExpr() {
		return globalState.toExpr();
	}

	public boolean isError() {
		return currentLoc.isErrorLoc() && backlog.size() == 0;
	}

	public XcfaLocation getCurrentLoc() {
		return currentLoc;
	}

	public Map<VarDecl<?>, Integer> getThreadLookup() {
		return threadLookup;
	}

	public S getGlobalState() {
		return globalState;
	}

	public Map<Integer, XcfaProcess> getBacklog() {
		return backlog;
	}

	public Map<VarDecl<?>, List<XcfaLabel.LoadXcfaLabel<?>>> getLoads() {
		return loads;
	}

	public Map<VarDecl<?>, List<XcfaLabel.StoreXcfaLabel<?>>> getStores() {
		return stores;
	}
}
