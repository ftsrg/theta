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
package hu.bme.mit.theta.xcfa.analysis.declarative.oota;

import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.cat.models.CoherenceMemory;
import hu.bme.mit.theta.cat.solver.DatalogOnlyMemoryModelBuilder;
import hu.bme.mit.theta.cat.solver.MemoryModelBuilder;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaProcess;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.decl.Decls.Const;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;

public class XcfaDeclarativeState<S extends ExprState> implements ExprState {
	private final boolean unsafe;
	private final Integer currentProcess;
	private final XcfaLocation currentLoc;
	private final Map<Integer, XcfaProcess> backlog;
	private final Map<VarDecl<?>, Integer> threadLookup;
	private final S state;
	private final Map<VarDecl<?>, List<Tuple2<XcfaLabel.StoreXcfaLabel<?>, ConstDecl<?>>>> stores;
	private final Map<VarDecl<?>, List<Tuple2<XcfaLabel.LoadXcfaLabel<?>, ConstDecl<?>>>> revisitableLoads;
	private final Integer memoryCount;
	private final Collection<Expr<BoolType>> assignments;
	private final MemoryModelBuilder memoryModelBuilder;
	private final Object lastPo;
	private final Expr<BoolType> invariant;

	private XcfaDeclarativeState(
			final boolean unsafe, final Integer currentProcess, final XcfaLocation currentLoc, Map<Integer, XcfaProcess> backlog,
			final Map<VarDecl<?>, Integer> threadLookup, final S state,
			final Map<VarDecl<?>, List<Tuple2<XcfaLabel.StoreXcfaLabel<?>, ConstDecl<?>>>> stores,
			final Map<VarDecl<?>, List<Tuple2<XcfaLabel.LoadXcfaLabel<?>, ConstDecl<?>>>> revisitableLoads, final Integer memoryCount,
			final Collection<Expr<BoolType>> assignments, final MemoryModelBuilder memoryModelBuilder, final Object lastPo, final Expr<BoolType> invariant) {
		this.unsafe = unsafe;
		this.currentProcess = currentProcess;
		this.currentLoc = currentLoc;
		this.backlog = backlog;
		this.threadLookup = threadLookup;
		this.state = state;
		this.stores = stores;
		this.revisitableLoads = revisitableLoads;
		this.memoryCount = memoryCount;
		this.assignments = assignments;
		this.memoryModelBuilder = memoryModelBuilder;
		if(lastPo == null) {
			this.lastPo = new Object();
			this.memoryModelBuilder.addProgramLoc(this.lastPo);
		} else {
			this.lastPo = lastPo;
		}
		checkState(this.memoryModelBuilder.getIndexOf(this.lastPo) != null, "lastPo should be added as a program loc!");
		this.invariant = invariant;
	}


	public static <S extends ExprState> XcfaDeclarativeState<S> fromParams(final XcfaLocation initLoc, final S s) {
		return fromParams(initLoc.isErrorLoc(), -1, initLoc, Map.of(), Map.of(), s, Map.of(), Map.of(), 0, List.of(), DatalogOnlyMemoryModelBuilder.create(new CoherenceMemory()), null, True());
	}


	private static <S extends ExprState> XcfaDeclarativeState<S> fromParams(
			final boolean unsafe, final Integer currentProcess, final XcfaLocation currentLoc,
			final Map<Integer, XcfaProcess> backlog, final Map<VarDecl<?>, Integer> threadLookup, final S state,
			final Map<VarDecl<?>, List<Tuple2<XcfaLabel.StoreXcfaLabel<?>, ConstDecl<?>>>> stores,
			final Map<VarDecl<?>, List<Tuple2<XcfaLabel.LoadXcfaLabel<?>, ConstDecl<?>>>> revisitableLoads, final Integer memoryCount,
			final Collection<Expr<BoolType>> assignments, final MemoryModelBuilder memoryModelBuilder, final Object lastPo,
			final Expr<BoolType> invariant) {
		return new XcfaDeclarativeState<S>(unsafe, currentProcess, currentLoc, backlog, threadLookup, state, stores, revisitableLoads, memoryCount, assignments, memoryModelBuilder, lastPo, invariant);
	}


	public Collection<XcfaDeclarativeState<S>> write(final XcfaLabel.StoreXcfaLabel<?> xcfaLabel) {
		final MemoryModelBuilder newMemoryModelBuilder = memoryModelBuilder.duplicate();
		Map<VarDecl<?>, List<Tuple2<XcfaLabel.StoreXcfaLabel<?>, ConstDecl<?>>>> newStores = new LinkedHashMap<>();
		stores.forEach((varDecl, tuple2s) -> newStores.put(varDecl, new ArrayList<>(tuple2s)));
		final List<Expr<BoolType>> newAssignments = new ArrayList<>(assignments);

		Object newLastPo = lastPo;
		newMemoryModelBuilder.addProgramLoc(currentProcess);

		newMemoryModelBuilder.addProgramLoc(xcfaLabel.getGlobal());
		newMemoryModelBuilder.addWriteProgramLoc(xcfaLabel, currentProcess, xcfaLabel.getGlobal());
		final ConstDecl<?> dataflow = Const("ARGdataflowW" + memoryCount, xcfaLabel.getLocal().getType());

		newAssignments.add(Eq(dataflow.getRef(), xcfaLabel.getLocal().getRef()));
		newMemoryModelBuilder.addPoEdge(newLastPo, xcfaLabel);
		newLastPo = xcfaLabel;

		newStores.putIfAbsent(xcfaLabel.getGlobal(), new ArrayList<>());
		newStores.get(xcfaLabel.getGlobal()).add(Tuple2.of(xcfaLabel, dataflow));

		final List<Tuple2<XcfaLabel.LoadXcfaLabel<?>, ConstDecl<?>>> revisitableLoads = this.revisitableLoads.get(xcfaLabel.getGlobal());
		List<XcfaDeclarativeState<S>> newStates = new ArrayList<>();
		if (revisitableLoads != null && revisitableLoads.size() > 0) {
			for (long i = 0; i < (1L << revisitableLoads.size()); i++) { // every subset (binary counting, bit match means choosing the element)
				Collection<Tuple2<XcfaLabel.LoadXcfaLabel<?>, ConstDecl<?>>> chosenLoads = new LinkedHashSet<>();
				List<Expr<BoolType>> expandedAssignments = new ArrayList<>(newAssignments);
				final MemoryModelBuilder duplicate = newMemoryModelBuilder.duplicate();

				for (int i1 = 0; i1 < revisitableLoads.size(); i1++) {
					if ((i & (1L << i1)) > 0) {
						chosenLoads.add(revisitableLoads.get(i1));
						expandedAssignments.add(Eq(dataflow.getRef(), revisitableLoads.get(i1).get2().getRef()));
						duplicate.addRfEdge(xcfaLabel, revisitableLoads.get(i1).get1());
					}
				}
				Map<VarDecl<?>, List<Tuple2<XcfaLabel.LoadXcfaLabel<?>, ConstDecl<?>>>> newLoads = new LinkedHashMap<>();
				this.revisitableLoads.forEach((varDecl, tuple2s) -> newLoads.put(varDecl, new ArrayList<>(tuple2s.stream().filter(objects -> !chosenLoads.contains(objects)).collect(Collectors.toList()))));
				final XcfaDeclarativeState<S> newState = fromParams(unsafe, currentProcess, currentLoc, backlog, threadLookup, state, newStores, newLoads, memoryCount + 1, expandedAssignments, duplicate, newLastPo, invariant);
				newStates.add(newState);
			}
		} else {
			final XcfaDeclarativeState<S> newState = fromParams(unsafe, currentProcess, currentLoc, backlog, threadLookup, state, newStores, this.revisitableLoads, memoryCount + 1, newAssignments, newMemoryModelBuilder, newLastPo, invariant);
			newStates.add(newState);
		}
		return newStates;
	}

	public Collection<XcfaDeclarativeState<S>> read(final XcfaLabel.LoadXcfaLabel<?> xcfaLabel) {
		final MemoryModelBuilder newMemoryModelBuilder = memoryModelBuilder.duplicate();
		Object newLastPo = lastPo;
		newMemoryModelBuilder.addProgramLoc(currentProcess);

		newMemoryModelBuilder.addProgramLoc(xcfaLabel.getGlobal());
		newMemoryModelBuilder.addReadProgramLoc(xcfaLabel, currentProcess, xcfaLabel.getGlobal());
		final ConstDecl<?> dataflow = Const("ARGdataflowR" + memoryCount, xcfaLabel.getLocal().getType());
		final List<Expr<BoolType>> newAssignments = new ArrayList<>(assignments);
		newAssignments.add(Eq(xcfaLabel.getLocal().getRef(), dataflow.getRef()));

		newMemoryModelBuilder.addPoEdge(newLastPo, xcfaLabel);
		newLastPo = xcfaLabel;

		final List<Tuple2<XcfaLabel.StoreXcfaLabel<?>, ConstDecl<?>>> stores = this.stores.get(xcfaLabel.getGlobal());
		List<XcfaDeclarativeState<S>> newStates = new ArrayList<>();
		for (Tuple2<XcfaLabel.StoreXcfaLabel<?>, ConstDecl<?>> store : stores) {
			final MemoryModelBuilder duplicate = newMemoryModelBuilder.duplicate();
			duplicate.addRfEdge(store.get1(), xcfaLabel);
			final ArrayList<Expr<BoolType>> expandedAssignments = new ArrayList<>(newAssignments);
			expandedAssignments.add(Eq(dataflow.getRef(), store.get2().getRef()));
			final XcfaDeclarativeState<S> newState = fromParams(unsafe, currentProcess, currentLoc, backlog, threadLookup, state, this.stores, this.revisitableLoads, memoryCount + 1, expandedAssignments, duplicate, newLastPo, invariant);
			newStates.add(newState);
		}

		Map<VarDecl<?>, List<Tuple2<XcfaLabel.LoadXcfaLabel<?>, ConstDecl<?>>>> newLoads = new LinkedHashMap<>();
		revisitableLoads.forEach((varDecl, tuple2s) -> newLoads.put(varDecl, new ArrayList<>(tuple2s)));
		newLoads.putIfAbsent(xcfaLabel.getGlobal(), new ArrayList<>());
		newLoads.get(xcfaLabel.getGlobal()).add(Tuple2.of(xcfaLabel, dataflow));
		final XcfaDeclarativeState<S> newState = fromParams(unsafe, currentProcess, currentLoc, backlog, threadLookup, state, this.stores, newLoads, memoryCount + 1, newAssignments, newMemoryModelBuilder, newLastPo, invariant);
		newStates.add(newState);
		return newStates;
	}

	public XcfaDeclarativeState<S> startthreads(final XcfaLabel.StartThreadXcfaLabel startThreadXcfaLabel) {
		final Map<Integer, XcfaProcess> newBacklog = new LinkedHashMap<>(backlog);
		final Map<VarDecl<?>, Integer> newThreadLookup = new LinkedHashMap<>(threadLookup);
		final MemoryModelBuilder newMemoryModelBuilder = memoryModelBuilder.duplicate();
		final XcfaProcess process = startThreadXcfaLabel.getProcess();
		newBacklog.put(newThreadLookup.size(), process);
		newThreadLookup.put(startThreadXcfaLabel.getKey(), newThreadLookup.size());
		newMemoryModelBuilder.addProgramLoc(getSingleton(Tuple2.of(newThreadLookup.size(), XcfaDeclarativeState.ProcessLabel.START)));
		newMemoryModelBuilder.addPoEdge(lastPo, getSingleton(Tuple2.of(newThreadLookup.size(), XcfaDeclarativeState.ProcessLabel.START)));
		return fromParams(unsafe, currentProcess, currentLoc, newBacklog, newThreadLookup, state, stores, revisitableLoads, memoryCount, assignments, newMemoryModelBuilder, lastPo, invariant);
	}

	public XcfaDeclarativeState<S> jointhreads(final XcfaLabel.JoinThreadXcfaLabel joinThreadXcfaLabel) {
		final MemoryModelBuilder newMemoryModelBuilder = memoryModelBuilder.duplicate();
		final Object newLastPo = new Object();
		newMemoryModelBuilder.addProgramLoc(newLastPo);
		newMemoryModelBuilder.addPoEdge(lastPo, newLastPo);
		newMemoryModelBuilder.addProgramLoc(getSingleton(Tuple2.of(threadLookup.get(joinThreadXcfaLabel.getKey()), XcfaDeclarativeState.ProcessLabel.END)));
		newMemoryModelBuilder.addPoEdge(getSingleton((Tuple2.of(threadLookup.get(joinThreadXcfaLabel.getKey()), XcfaDeclarativeState.ProcessLabel.END))), newLastPo);
		return fromParams(unsafe, currentProcess, currentLoc, backlog, threadLookup, state, stores, revisitableLoads, memoryCount, assignments, newMemoryModelBuilder, newLastPo, invariant);
	}

	public XcfaDeclarativeState<S> advance(final S succState, final XcfaDeclarativeAction action) {
		final Map<Integer, XcfaProcess> newBackLog = new LinkedHashMap<>(backlog);
		final MemoryModelBuilder newMemoryModelBuilder = memoryModelBuilder.duplicate();
		final Integer process;
		final Object newLastPo = new Object();
		newMemoryModelBuilder.addProgramLoc(newLastPo);
		if(action instanceof XcfaDeclarativeAction.XcfaDeclarativeThreadChangeAction) {
			process = ((XcfaDeclarativeAction.XcfaDeclarativeThreadChangeAction) action).getProcess();
			final Tuple2<Integer, XcfaDeclarativeState.ProcessLabel> currentEnd = getSingleton(Tuple2.of(currentProcess, XcfaDeclarativeState.ProcessLabel.END));
			final Tuple2<Integer, XcfaDeclarativeState.ProcessLabel> newSource = getSingleton(Tuple2.of(process, XcfaDeclarativeState.ProcessLabel.START));
			newMemoryModelBuilder.addProgramLoc(currentEnd);
			newMemoryModelBuilder.addProgramLoc(newSource);
			newMemoryModelBuilder.addPoEdge(lastPo, currentEnd);
			newMemoryModelBuilder.addPoEdge(newSource, newLastPo);
			if(currentProcess >= 0)
				newBackLog.remove(currentProcess);
		} else {
			process = currentProcess;
			newMemoryModelBuilder.addPoEdge(lastPo, newLastPo);
		}
		return fromParams(unsafe || action.getTarget().isErrorLoc(), process, action.getTarget(), newBackLog, threadLookup, succState, stores, revisitableLoads, memoryCount, List.of(), newMemoryModelBuilder, newLastPo, True());
	}


	public boolean isError() {
		return unsafe && backlog.size() == 0 && revisitableLoads.values().stream().allMatch(r -> r.size() == 0);
	}

	@Override
	public boolean isBottom() {
		return state.isBottom() || !memoryModelBuilder.check();
	}

	@Override
	public Expr<BoolType> toExpr() {
		return And(state.toExpr(), And(assignments), invariant);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		XcfaDeclarativeState<?> that = (XcfaDeclarativeState<?>) o;
		return unsafe == that.unsafe && currentProcess.equals(that.currentProcess) && currentLoc.equals(that.currentLoc) && backlog.equals(that.backlog) && state.equals(that.state) && stores.equals(that.stores) && revisitableLoads.equals(that.revisitableLoads) && assignments.equals(that.assignments);
	}

	@Override
	public int hashCode() {
		return Objects.hash(unsafe, currentProcess, currentLoc, backlog, state, stores, revisitableLoads, assignments);
	}

	@Override
	public String toString() {
		return "XcfaDeclarativeState{" +
				"unsafe=" + unsafe +
				", currentLoc=" + currentLoc +
				", backlog=" + backlog.size() +
				", state=" + state +
				", stores=" + stores +
				", revisitableLoads=" + revisitableLoads +
				", assignments=" + assignments +
				'}';
	}

	public XcfaLocation getCurrentLoc() {
		return currentLoc;
	}

	public Map<Integer, XcfaProcess> getBacklog() {
		return backlog;
	}

	public Map<VarDecl<?>, Integer> getThreadLookup() {
		return threadLookup;
	}

	public Collection<Expr<BoolType>> getAssignments() {
		return assignments;
	}

	public Integer getCurrentProcess() {
		return currentProcess;
	}

	public Integer getMemoryCount() {
		return memoryCount;
	}

	public Map<VarDecl<?>, List<Tuple2<XcfaLabel.LoadXcfaLabel<?>, ConstDecl<?>>>> getRevisitableLoads() {
		return revisitableLoads;
	}

	public Map<VarDecl<?>, List<Tuple2<XcfaLabel.StoreXcfaLabel<?>, ConstDecl<?>>>> getStores() {
		return stores;
	}

	public MemoryModelBuilder getMemoryModelBuilder() {
		return memoryModelBuilder;
	}

	public S getState() {
		return state;
	}

	public boolean isUnsafe() {
		return unsafe;
	}

	public Expr<BoolType> getInvariant() {
		return invariant;
	}

	public XcfaDeclarativeState<S> addInvariant(Expr<BoolType> invariant) {
		return fromParams(unsafe, currentProcess, currentLoc, backlog, threadLookup, state, stores, revisitableLoads, memoryCount, assignments, memoryModelBuilder, lastPo, And(this.invariant, invariant));
	}

	private enum ProcessLabel {
		START,
		END
	}

	private static final Map<Object, Object> singletonStore = new LinkedHashMap<>();
	private static <T> T getSingleton(T o) {
		singletonStore.putIfAbsent(o, o);
		//noinspection unchecked
		return (T) singletonStore.get(o);
	}
}
