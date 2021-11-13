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
package hu.bme.mit.theta.xcfa.analysis.impl.interleavings;

import com.google.common.collect.ImmutableMap;
import hu.bme.mit.theta.analysis.PartialOrd;
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

public class XcfaState<S extends ExprState> extends hu.bme.mit.theta.xcfa.analysis.common.XcfaState<S> {
	private final Map<Integer, XcfaLocation> processLocs;
	private final Collection<Integer> enabledProcesses;
	private final Collection<Integer> oldEnabledProcesses;
	private final Map<VarDecl<?>, Integer> threadLookup;
	private final Map<Integer, Collection<Integer>> waitForEnd;
	private final XcfaAction lastAction;
	private final S globalState;

	protected XcfaState(final Map<XcfaLocation, Boolean> processLocs, final S globalState) {
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
		oldEnabledProcesses = null;
		lastAction = null;
	}

	protected XcfaState(final Map<Integer, XcfaLocation> processLocs, final Collection<Integer> enabledProcesses, Collection<Integer> oldEnabledProcesses, final Map<VarDecl<?>, Integer> threadLookup, final S globalState, final Map<Integer, Collection<Integer>> waitForEnd, final XcfaAction lastAction) {
		this.processLocs = ImmutableMap.copyOf(checkNotNull(processLocs));
		this.enabledProcesses = new ArrayList<>(checkNotNull(enabledProcesses));
		this.oldEnabledProcesses = oldEnabledProcesses; // this can deliberately be null!
		this.threadLookup = ImmutableMap.copyOf((checkNotNull(threadLookup)));
		this.globalState = checkNotNull(globalState);
		this.waitForEnd = waitForEnd.entrySet().stream().map(e -> Map.entry(e.getKey(), new ArrayList<>(e.getValue()))).collect(Collectors.toMap(Map.Entry::getKey, Map.Entry::getValue));
		this.lastAction = lastAction;

		final Collection<Integer> endOrError = new ArrayList<>();
		this.processLocs.forEach((integer, xcfaLocation) -> {if(xcfaLocation.isEndLoc() || xcfaLocation.isErrorLoc()) endOrError.add(integer);});
		this.waitForEnd.forEach((integer, integers) -> {
			integers.removeIf(endOrError::contains);
		});
		final List<Map.Entry<Integer, Collection<Integer>>> collect = this.waitForEnd.entrySet().stream().filter(e -> e.getValue().size() == 0).collect(Collectors.toList());
		for (Map.Entry<Integer, Collection<Integer>> toRemove : collect) {
			this.waitForEnd.remove(toRemove.getKey());
			this.enabledProcesses.add(toRemove.getKey());
		}
	}

	public static <S extends ExprState> XcfaState<S> create(final Map<XcfaLocation, Boolean> processLocs, final S globalState) {
		return new XcfaState<>(processLocs, globalState);
	}

	protected XcfaState<S> withParams(final Map<Integer, XcfaLocation> processLocs, final Collection<Integer> enabledProcesses, Collection<Integer> oldEnabledProcesses, final Map<VarDecl<?>, Integer> threadLookup, final S globalState, final Map<Integer, Collection<Integer>> waitForEnd, final XcfaAction lastAction) {
		return new XcfaState<S>(processLocs, enabledProcesses, oldEnabledProcesses, threadLookup, globalState, waitForEnd, lastAction);
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

	@Override
	public XcfaLocation getCurrentLoc() {
		return lastAction == null ? processLocs.get(enabledProcesses.stream().findAny().get()) : lastAction.getTarget();
	}

	public Map<VarDecl<?>, Integer> getThreadLookup() {
		return threadLookup;
	}

	public Collection<Integer> getOldEnabledProcesses() {
		return oldEnabledProcesses;
	}

	public XcfaState<S> advance(final S succState, final XcfaAction action) {
		checkState(processLocs.containsKey(action.getProcess()));
		final Map<Integer, XcfaLocation> newProcessLocs = new LinkedHashMap<>(processLocs);
		newProcessLocs.put(action.getProcess(), action.getTarget());
		return withParams(newProcessLocs, enabledProcesses, oldEnabledProcesses, threadLookup, succState, waitForEnd, action);
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
		return withParams(processLocs, enabledProcesses, oldEnabledProcesses, threadLookup, globalState, waitForEnd, lastAction);
	}

	public XcfaState<S> jointhreads(final Integer process, final List<XcfaLabel.JoinThreadXcfaLabel> joinThreadList) {
		final Map<Integer, Collection<Integer>> newWaitForEnd = new LinkedHashMap<>(waitForEnd);
		final List<Integer> newEnabledProcesses = new ArrayList<>(enabledProcesses);
		for (XcfaLabel.JoinThreadXcfaLabel joinThreadXcfaLabel : joinThreadList) {
			newEnabledProcesses.remove(process);
			newWaitForEnd.putIfAbsent(process, new LinkedHashSet<>());
			newWaitForEnd.get(process).add(threadLookup.get(joinThreadXcfaLabel.getKey()));
		}
		return withParams(processLocs, newEnabledProcesses, oldEnabledProcesses, threadLookup, globalState, newWaitForEnd, lastAction);
	}

	public Map<Integer, Collection<Integer>> getWaitForEnd() {
		return waitForEnd;
	}

	public XcfaAction getLastAction() {
		return lastAction;
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

	public boolean isLeq(final PartialOrd<S> partialOrd, final XcfaState<S> state2) {
		return /*threadLookup.size() <= state2.threadLookup.size() &&
		threadLookup.entrySet().stream().noneMatch(e -> enabledProcesses.contains(e.getValue()) ^ (state2.threadLookup.containsKey(e.getKey()) && state2.enabledProcesses.contains(state2.threadLookup.get(e.getKey())))) && */
		partialOrd.isLeq(globalState, state2.globalState);
	}

	public XcfaState<S> atomicbegin(final Integer process, final Boolean atomicBegin) {
		if(atomicBegin == null || (!atomicBegin && oldEnabledProcesses == null)) return this;
		else if(atomicBegin) {
			final ArrayList<Integer> newEnabledProcesses = new ArrayList<>();
			checkState(enabledProcesses.contains(process), "Not active process cannot become atomic!");
			newEnabledProcesses.add(process);
			return withParams(processLocs, newEnabledProcesses, oldEnabledProcesses == null ? enabledProcesses : oldEnabledProcesses, threadLookup, globalState, waitForEnd, lastAction);
		} else {
			checkState(enabledProcesses.contains(process), "Not active process cannot become non-atomic!");
			return withParams(processLocs, oldEnabledProcesses, null, threadLookup, globalState, waitForEnd, lastAction);
		}
	}
}
