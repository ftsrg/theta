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
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.cat.models.CoherenceMemory;
import hu.bme.mit.theta.cat.solver.BoolSmtMemoryModelBuilder;
import hu.bme.mit.theta.cat.solver.MemoryModelBuilder;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.MutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaProcess;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;

public class XcfaDeclarativeState<S extends ExprState> implements ExprState {
	private final boolean unsafe;
	private final Integer currentProcess;
	private final XcfaLocation currentLoc;
	private final Map<Integer, XcfaProcess> backlog;
	private final Map<VarDecl<?>, Integer> threadLookup;
	private final S globalState;
	private final Expr<BoolType> invariant;
	private final Map<VarDecl<?>, List<Tuple2<XcfaLabel.LoadXcfaLabel<?>, S>>> loads;
	private final Map<VarDecl<?>, List<Tuple2<XcfaLabel.StoreXcfaLabel<?>, S>>> stores;
	private final MemoryModelBuilder memoryModelBuilder;

	private XcfaDeclarativeState(final boolean unsafe, final Integer currentProcess, final XcfaLocation currentLoc, final Map<Integer, XcfaProcess> backlog, final Map<VarDecl<?>, Integer> threadLookup, final S globalState, Expr<BoolType> invariant, final Map<VarDecl<?>, List<Tuple2<XcfaLabel.LoadXcfaLabel<?>, S>>> loads, final Map<VarDecl<?>, List<Tuple2<XcfaLabel.StoreXcfaLabel<?>, S>>> stores, final MemoryModelBuilder memoryModelBuilder) {
		this.unsafe = unsafe;
		this.currentProcess = currentProcess;
		this.currentLoc = checkNotNull(currentLoc);
		this.backlog = ImmutableMap.copyOf(checkNotNull(backlog));
		this.threadLookup = ImmutableMap.copyOf(checkNotNull(threadLookup));
		this.globalState = checkNotNull(globalState);
		this.invariant = invariant;
		this.loads = ImmutableMap.copyOf(checkNotNull(loads));
		this.stores = ImmutableMap.copyOf(checkNotNull(stores));
		this.memoryModelBuilder = memoryModelBuilder;
	}

	public static <S extends ExprState> XcfaDeclarativeState<S> fromParams(final boolean unsafe, final Integer currentProcess, final XcfaLocation currentLoc, final Map<Integer, XcfaProcess> backlog, final Map<VarDecl<?>, Integer> threadLookup, final S globalState, final Expr<BoolType> invariant, final Map<VarDecl<?>, List<Tuple2<XcfaLabel.LoadXcfaLabel<?>, S>>> loads, final Map<VarDecl<?>, List<Tuple2<XcfaLabel.StoreXcfaLabel<?>, S>>> stores, final MemoryModelBuilder memoryModelBuilder) {
		return new XcfaDeclarativeState<S>(unsafe, currentProcess, currentLoc, backlog, threadLookup, globalState, invariant, loads, stores, memoryModelBuilder);
	}

	public static <S extends ExprState> XcfaDeclarativeState<S> create(final XcfaLocation currentLoc, final S globalState) {
		return fromParams(currentLoc.isErrorLoc(), -1, currentLoc, Map.of(), Map.of(), globalState, True(), Map.of(), Map.of(), BoolSmtMemoryModelBuilder.create(new CoherenceMemory()));
	}

	@Override
	public boolean isBottom() {
		return globalState.isBottom();
	}

	@Override
	public Expr<BoolType> toExpr() {
		return And(globalState.toExpr(), invariant);
	}

	public boolean isError() {
		if(unsafe && backlog.size() == 0) {
			return true; // TODO
		}
		return false;
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

	public Map<VarDecl<?>, List<Tuple2<XcfaLabel.LoadXcfaLabel<?>, S>>> getLoads() {
		return loads;
	}

	public Map<VarDecl<?>, List<Tuple2<XcfaLabel.StoreXcfaLabel<?>, S>>> getStores() {
		return stores;
	}

	public XcfaDeclarativeState<S> atomicbegin(final Boolean atomicBegin) {
		return fromParams(unsafe, currentProcess, currentLoc, backlog, threadLookup, globalState, invariant, loads, stores, memoryModelBuilder.duplicate());
	}

	public XcfaDeclarativeState<S> startthreads(final List<XcfaLabel.StartThreadXcfaLabel> startThreadList) {
		final Map<Integer, XcfaProcess> newBacklog = new LinkedHashMap<>(backlog);
		final Map<VarDecl<?>, Integer> newThreadLookup = new LinkedHashMap<>(threadLookup);
		for (XcfaLabel.StartThreadXcfaLabel startThreadXcfaLabel : startThreadList) {
			final XcfaProcess process = startThreadXcfaLabel.getProcess();
			newBacklog.put(threadLookup.size(), process);
			newThreadLookup.put(startThreadXcfaLabel.getKey(), threadLookup.size());
		}
		return fromParams(unsafe, currentProcess, currentLoc, newBacklog, newThreadLookup, globalState, invariant, loads, stores, memoryModelBuilder.duplicate());
	}

	public XcfaDeclarativeState<S> jointhreads(final List<XcfaLabel.JoinThreadXcfaLabel> joinThreadList) {
		return fromParams(unsafe, currentProcess, currentLoc, backlog, threadLookup, globalState, invariant,  loads, stores, memoryModelBuilder.duplicate());
	}

	public XcfaDeclarativeState<S> advance(final S succState, final XcfaDeclarativeAction action) {
		final Map<Integer, XcfaProcess> newBackLog = new LinkedHashMap<>(backlog);
		final Integer process;
		if(action instanceof XcfaDeclarativeAction.XcfaDeclarativeThreadChangeAction) {
			process = ((XcfaDeclarativeAction.XcfaDeclarativeThreadChangeAction) action).getProcess();
			if(currentProcess >= 0)
				newBackLog.remove(currentProcess);
		} else process = currentProcess;
		return fromParams(unsafe || action.getTarget().isErrorLoc(), process, action.getTarget(), newBackLog, threadLookup, succState, invariant,  loads, stores, memoryModelBuilder.duplicate());
	}

	public XcfaDeclarativeState<S> memory(final List<XcfaLabel> memory) {
		final Map<VarDecl<?>, List<Tuple2<XcfaLabel.LoadXcfaLabel<?>, S>>> newLoads = new LinkedHashMap<>(loads);
		final Map<VarDecl<?>, List<Tuple2<XcfaLabel.StoreXcfaLabel<?>, S>>> newStores = new LinkedHashMap<>(stores);
		for (XcfaLabel xcfaLabel : memory) {
			if(xcfaLabel instanceof XcfaLabel.LoadXcfaLabel) {
				newLoads.putIfAbsent(((XcfaLabel.LoadXcfaLabel<?>) xcfaLabel).getGlobal(), new ArrayList<>());
				newLoads.get(((XcfaLabel.LoadXcfaLabel<?>) xcfaLabel).getGlobal()).add(Tuple2.of((XcfaLabel.LoadXcfaLabel<?>) xcfaLabel, getUniqeState(globalState)));
			} else if (xcfaLabel instanceof XcfaLabel.StoreXcfaLabel) {
				newStores.putIfAbsent(((XcfaLabel.StoreXcfaLabel<?>) xcfaLabel).getGlobal(), new ArrayList<>());
				newStores.get(((XcfaLabel.StoreXcfaLabel<?>) xcfaLabel).getGlobal()).add(Tuple2.of((XcfaLabel.StoreXcfaLabel<?>) xcfaLabel, globalState));
			} else if (xcfaLabel instanceof XcfaLabel.FenceXcfaLabel) {

			} else {
				throw new UnsupportedOperationException("Label type not recognized: " + xcfaLabel);
			}
		}
		return fromParams(unsafe, currentProcess, currentLoc, backlog, threadLookup, globalState, invariant,  newLoads, newStores, memoryModelBuilder.duplicate());
	}

	private S getUniqeState(S globalState) {
		if(globalState.isBottom()) return globalState;
		if(globalState instanceof ExplState) {
			final Valuation val = ((ExplState) globalState).getVal();
			final MutableValuation newVal = new MutableValuation();
			val.toMap().forEach((decl, litExpr) -> {
			});
		}
		return globalState; //TODO
	}

	public XcfaDeclarativeState<S> addInvariant(final Expr<BoolType> invariant) {
		return fromParams(unsafe, currentProcess, currentLoc, backlog, threadLookup, globalState, invariant,  loads, stores, memoryModelBuilder.duplicate());
	}

	@Override
	public String toString() {
		return "XcfaDeclarativeState{" +
				"unsafe=" + unsafe +
				", currentLoc=" + currentLoc +
				", backlog=" + backlog +
				", threadLookup=" + threadLookup +
				", globalState=" + globalState +
				", invariant=" + invariant +
				", loads=" + loads +
				", stores=" + stores +
				'}';
	}

	public boolean isUnsafe() {
		return unsafe;
	}

	public Integer getCurrentProcess() {
		return currentProcess;
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		XcfaDeclarativeState<?> that = (XcfaDeclarativeState<?>) o;
		return currentProcess.equals(that.currentProcess) && Objects.equals(currentLoc, that.currentLoc) && backlog.size() == that.backlog.size() && globalState.equals(that.globalState) && loads.equals(that.loads) && stores.equals(that.stores) && Objects.equals(invariant, that.invariant);
	}

	@Override
	public int hashCode() {
		return Objects.hash(currentProcess, currentLoc, backlog.size(), globalState, invariant, loads, stores);
	}
}
