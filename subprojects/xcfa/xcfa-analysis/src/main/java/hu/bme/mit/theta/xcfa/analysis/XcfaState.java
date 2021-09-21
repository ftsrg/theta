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
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

public final class XcfaState<S extends ExprState> implements ExprState {
	private final Map<Integer, XcfaLocation> processLocs;
	private final Collection<Integer> enabledProcesses;
	private final Map<VarDecl<?>, Integer> threadLookup;
	private final Map<Integer, Collection<Integer>> waitForEnd;
	private final S globalState;

	private XcfaState(final Map<XcfaLocation, Boolean> processLocs, final S globalState) {
		checkNotNull(processLocs);
		this.processLocs = new LinkedHashMap<>();
		this.enabledProcesses = new ArrayList<>();
		processLocs.forEach((xcfaLocation, aBoolean) -> {
			this.processLocs.put(this.processLocs.size(), xcfaLocation);
			if(aBoolean) this.enabledProcesses.add(this.processLocs.size() - 1);
		});
		this.globalState = checkNotNull(globalState);
		waitForEnd = new LinkedHashMap<>();
		this.threadLookup = new LinkedHashMap<>();
	}

	private XcfaState(final Map<Integer, XcfaLocation> processLocs, final Collection<Integer> enabledProcesses, final Map<VarDecl<?>, Integer> threadLookup, final S globalState, final Map<Integer, Collection<Integer>> waitForEnd) {
		this.processLocs = checkNotNull(processLocs);
		this.enabledProcesses = checkNotNull(enabledProcesses);
		this.threadLookup = checkNotNull(threadLookup);
		this.globalState = checkNotNull(globalState);
		this.waitForEnd = checkNotNull(waitForEnd);

		final Collection<Integer> endOrError = new ArrayList<>();
		processLocs.forEach((integer, xcfaLocation) -> {if(xcfaLocation.isEndLoc() || xcfaLocation.isErrorLoc()) endOrError.add(integer);});
		waitForEnd.forEach((integer, integers) -> {
			integers.removeIf(endOrError::contains);
		});
		final List<Map.Entry<Integer, Collection<Integer>>> collect = waitForEnd.entrySet().stream().filter(e -> e.getValue().size() == 0).collect(Collectors.toList());
		for (Map.Entry<Integer, Collection<Integer>> toRemove : collect) {
			this.waitForEnd.remove(toRemove.getKey());
			this.enabledProcesses.add(toRemove.getKey());
		}
	}

	public static <S extends ExprState> XcfaState<S> create(final Map<XcfaLocation, Boolean> processLocs, final S globalState) {
		return new XcfaState<>(processLocs, globalState);
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
		return new XcfaState<>(newProcessLocs, enabledProcesses, threadLookup, succState, waitForEnd);
	}

	public boolean isError() {
		return processLocs.values().stream().anyMatch(XcfaLocation::isErrorLoc);
	}

	public XcfaState<S> startthreads(final List<XcfaLabel.StartThreadXcfaLabel> startThreadList) {
		final Collection<Integer> enabledProcesses = new ArrayList<>(this.enabledProcesses);
		final Map<Integer, XcfaLocation> processLocs = new LinkedHashMap<>(this.processLocs);
		final LinkedHashMap<VarDecl<?>, Integer> threadLookup = new LinkedHashMap<>(this.threadLookup);
		for (XcfaLabel.StartThreadXcfaLabel startThreadXcfaLabel : startThreadList) {
			enabledProcesses.add(processLocs.size());
			threadLookup.put(startThreadXcfaLabel.getKey(), processLocs.size());
			processLocs.put(processLocs.size(), startThreadXcfaLabel.getProcess().getMainProcedure().getInitLoc());
		}
		return new XcfaState<>(processLocs, enabledProcesses, threadLookup, globalState, waitForEnd);
	}

	public XcfaState<S> jointhreads(final Integer process, final List<XcfaLabel.JoinThreadXcfaLabel> joinThreadList) {
		final Map<Integer, Collection<Integer>> newWaitForEnd = new LinkedHashMap<>(waitForEnd);
		for (XcfaLabel.JoinThreadXcfaLabel joinThreadXcfaLabel : joinThreadList) {
			enabledProcesses.remove(process);
			newWaitForEnd.putIfAbsent(process, new LinkedHashSet<>());
			newWaitForEnd.get(process).add(threadLookup.get(joinThreadXcfaLabel.getKey()));
		}
		return new XcfaState<>(processLocs, enabledProcesses, threadLookup, globalState, newWaitForEnd);
	}

	@Override
	public String toString() {
		return "XcfaState{" +
				"processLocs=" + processLocs +
				", enabledProcesses=" + enabledProcesses +
				", threadLookup=" + threadLookup +
				", waitForEnd=" + waitForEnd +
				", globalState=" + globalState +
				'}';
	}
}
