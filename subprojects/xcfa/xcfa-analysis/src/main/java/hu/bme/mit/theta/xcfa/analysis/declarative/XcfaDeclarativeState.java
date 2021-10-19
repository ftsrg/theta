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
import hu.bme.mit.theta.analysis.pred.PredState;
import hu.bme.mit.theta.cat.models.CoherenceMemory;
import hu.bme.mit.theta.cat.solver.BoolDatalogMemoryModelBuilder;
import hu.bme.mit.theta.cat.solver.MemoryModelBuilder;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;
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
import java.util.Set;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkNotNull;
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
	private final S globalState;
	private final Expr<BoolType> invariant;
	private final List<Expr<BoolType>> eqPrec;
	private final Map<VarDecl<?>, List<Tuple2<XcfaLabel.LoadXcfaLabel<?>, ConstDecl<?>>>> revisitableLoads;
	private final Map<VarDecl<?>, List<Tuple2<XcfaLabel.StoreXcfaLabel<?>, ConstDecl<?>>>> stores;
	private final MemoryModelBuilder memoryModelBuilder;
	private Integer counter;
	private final Object lastPo;

	private XcfaDeclarativeState(
			final boolean unsafe, final Integer currentProcess, final XcfaLocation currentLoc, final Map<Integer, XcfaProcess> backlog,
			final Map<VarDecl<?>, Integer> threadLookup, final S globalState, Expr<BoolType> invariant,
			final Map<VarDecl<?>, List<Tuple2<XcfaLabel.LoadXcfaLabel<?>, ConstDecl<?>>>> revisitableLoads,
			final Map<VarDecl<?>, List<Tuple2<XcfaLabel.StoreXcfaLabel<?>, ConstDecl<?>>>> stores,
			List<Expr<BoolType>> eqPrec, final MemoryModelBuilder memoryModelBuilder, Integer counter, final Object lastPo) {
		this.unsafe = unsafe;
		this.currentProcess = currentProcess;
		this.currentLoc = checkNotNull(currentLoc);
		this.backlog = ImmutableMap.copyOf(checkNotNull(backlog));
		this.threadLookup = ImmutableMap.copyOf(checkNotNull(threadLookup));
		this.globalState = checkNotNull(globalState);
		this.invariant = invariant;
		this.eqPrec = eqPrec;
		this.counter = counter;
		this.revisitableLoads = new LinkedHashMap<>();
		revisitableLoads.forEach((varDecl, tuple2s) -> this.revisitableLoads.put(varDecl, new ArrayList<>(tuple2s)));
		this.stores = new LinkedHashMap<>();
		stores.forEach((varDecl, tuple2s) -> this.stores.put(varDecl, new ArrayList<>(tuple2s)));
		this.memoryModelBuilder = memoryModelBuilder.duplicate();
		if(lastPo == null) {
			this.lastPo = new Object();
			this.memoryModelBuilder.addProgramLoc(this.lastPo);
		} else {
			this.lastPo = lastPo;
		}
		checkState(this.memoryModelBuilder.getIndexOf(this.lastPo) != null, "lastPo should be added as a program loc!");
	}

	public static <S extends ExprState> XcfaDeclarativeState<S> fromParams(final boolean unsafe, final Integer currentProcess, final XcfaLocation currentLoc, final Map<Integer, XcfaProcess> backlog, final Map<VarDecl<?>, Integer> threadLookup, final S globalState, final Expr<BoolType> invariant, final Map<VarDecl<?>, List<Tuple2<XcfaLabel.LoadXcfaLabel<?>, ConstDecl<?>>>> loads, final Map<VarDecl<?>, List<Tuple2<XcfaLabel.StoreXcfaLabel<?>, ConstDecl<?>>>> stores,  final List<Expr<BoolType>> eqPrec, final MemoryModelBuilder memoryModelBuilder, final Integer counter, final Object lastPo) {
		return new XcfaDeclarativeState<S>(unsafe, currentProcess, currentLoc, backlog, threadLookup, globalState, invariant, loads, stores, eqPrec, memoryModelBuilder, counter, lastPo);
	}

	public static <S extends ExprState> XcfaDeclarativeState<S> create(final XcfaLocation currentLoc, final S globalState) {
		return fromParams(currentLoc.isErrorLoc(), -1, currentLoc, Map.of(), Map.of(), globalState, True(), Map.of(), Map.of(), List.of(), BoolDatalogMemoryModelBuilder.create(new CoherenceMemory(), Z3SolverFactory.getInstance().createSolver()), 0, null);
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
		return unsafe && backlog.size() == 0 && revisitableLoads.values().stream().allMatch(v -> v.size() == 0);
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

	public Map<VarDecl<?>, List<Tuple2<XcfaLabel.LoadXcfaLabel<?>, ConstDecl<?>>>> getRevisitableLoads() {
		return revisitableLoads;
	}

	public Map<VarDecl<?>, List<Tuple2<XcfaLabel.StoreXcfaLabel<?>, ConstDecl<?>>>> getStores() {
		return stores;
	}

	public XcfaDeclarativeState<S> atomicbegin(final Boolean atomicBegin) {
		return fromParams(unsafe, currentProcess, currentLoc, backlog, threadLookup, globalState, invariant, revisitableLoads, stores, eqPrec, memoryModelBuilder.duplicate(), counter, lastPo);
	}

	public XcfaDeclarativeState<S> startthreads(final List<XcfaLabel.StartThreadXcfaLabel> startThreadList) {
		final Map<Integer, XcfaProcess> newBacklog = new LinkedHashMap<>(backlog);
		final Map<VarDecl<?>, Integer> newThreadLookup = new LinkedHashMap<>(threadLookup);
		final MemoryModelBuilder newMemoryModelBuilder = memoryModelBuilder.duplicate();
		for (XcfaLabel.StartThreadXcfaLabel startThreadXcfaLabel : startThreadList) {
			final XcfaProcess process = startThreadXcfaLabel.getProcess();
			newBacklog.put(newThreadLookup.size(), process);
			newThreadLookup.put(startThreadXcfaLabel.getKey(), newThreadLookup.size());
			newMemoryModelBuilder.addProgramLoc(getSingleton(Tuple2.of(newThreadLookup.size(), ProcessLabel.START)));
			newMemoryModelBuilder.addPoEdge(lastPo, getSingleton(Tuple2.of(newThreadLookup.size(), ProcessLabel.START)));
		}
		return fromParams(unsafe, currentProcess, currentLoc, newBacklog, newThreadLookup, globalState, invariant, revisitableLoads, stores, eqPrec, newMemoryModelBuilder, counter, lastPo);
	}

	public XcfaDeclarativeState<S> jointhreads(final List<XcfaLabel.JoinThreadXcfaLabel> joinThreadList) {
		final MemoryModelBuilder newMemoryModelBuilder = memoryModelBuilder.duplicate();
		if(joinThreadList.size() > 0) {
			final Object newLastPo = new Object();
			newMemoryModelBuilder.addProgramLoc(newLastPo);
			newMemoryModelBuilder.addPoEdge(lastPo, newLastPo);
			for (XcfaLabel.JoinThreadXcfaLabel joinThreadXcfaLabel : joinThreadList) {
				newMemoryModelBuilder.addProgramLoc(getSingleton(Tuple2.of(threadLookup.get(joinThreadXcfaLabel.getKey()), ProcessLabel.END)));
				newMemoryModelBuilder.addPoEdge(getSingleton((Tuple2.of(threadLookup.get(joinThreadXcfaLabel.getKey()), ProcessLabel.END))), newLastPo);
			}
			return fromParams(unsafe, currentProcess, currentLoc, backlog, threadLookup, globalState, invariant, revisitableLoads, stores, eqPrec, newMemoryModelBuilder, counter, newLastPo);
		}
		return fromParams(unsafe, currentProcess, currentLoc, backlog, threadLookup, globalState, invariant, revisitableLoads, stores, eqPrec, newMemoryModelBuilder, counter, lastPo);
	}

	public XcfaDeclarativeState<S> advance(final S succState, final XcfaDeclarativeAction action) {
		final Map<Integer, XcfaProcess> newBackLog = new LinkedHashMap<>(backlog);
		final MemoryModelBuilder newMemoryModelBuilder = memoryModelBuilder.duplicate();
		final Integer process;
		final Object newLastPo = new Object();
		newMemoryModelBuilder.addProgramLoc(newLastPo);
		if(action instanceof XcfaDeclarativeAction.XcfaDeclarativeThreadChangeAction) {
			process = ((XcfaDeclarativeAction.XcfaDeclarativeThreadChangeAction) action).getProcess();
			final Tuple2<Integer, ProcessLabel> currentEnd = getSingleton(Tuple2.of(currentProcess, ProcessLabel.END));
			final Tuple2<Integer, ProcessLabel> newSource = getSingleton(Tuple2.of(process, ProcessLabel.START));
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
		return fromParams(unsafe || action.getTarget().isErrorLoc(), process, action.getTarget(), newBackLog, threadLookup, succState, True(), revisitableLoads, stores, eqPrec, newMemoryModelBuilder, counter, newLastPo);
	}

	public Collection<XcfaDeclarativeState<S>> memory(final XcfaLabel xcfaLabel) {
		final MemoryModelBuilder newMemoryModelBuilder = memoryModelBuilder.duplicate();
		Object newLastPo = lastPo;
		newMemoryModelBuilder.addProgramLoc(currentProcess);
		if(xcfaLabel instanceof XcfaLabel.LoadXcfaLabel) {

			newMemoryModelBuilder.addProgramLoc(((XcfaLabel.LoadXcfaLabel<?>) xcfaLabel).getGlobal());
			newMemoryModelBuilder.addReadProgramLoc(xcfaLabel, currentProcess, ((XcfaLabel.LoadXcfaLabel<?>) xcfaLabel).getGlobal());
			final ConstDecl<?> dataflow = Const("ARGdataflowR" + counter++, ((XcfaLabel.LoadXcfaLabel<?>) xcfaLabel).getLocal().getType());
			Expr<BoolType> invariant = And(this.invariant, Eq(dataflow.getRef(), ((XcfaLabel.LoadXcfaLabel<?>) xcfaLabel).getLocal().getRef()));
			List<Expr<BoolType>> eqPrec = new ArrayList<>(this.eqPrec);
			eqPrec.add(Eq(dataflow.getRef(), ((XcfaLabel.LoadXcfaLabel<?>) xcfaLabel).getLocal().getRef()));
			newMemoryModelBuilder.addPoEdge(newLastPo, xcfaLabel);
			newLastPo = xcfaLabel;

			final List<Tuple2<XcfaLabel.StoreXcfaLabel<?>, ConstDecl<?>>> stores = this.stores.get(((XcfaLabel.LoadXcfaLabel<?>) xcfaLabel).getGlobal());
			List<XcfaDeclarativeState<S>> newStates = new ArrayList<>();
			for (Tuple2<XcfaLabel.StoreXcfaLabel<?>, ConstDecl<?>> store : stores) {
				final XcfaDeclarativeState<S> newState;
				final MemoryModelBuilder duplicate = newMemoryModelBuilder.duplicate();
				duplicate.addRfEdge(store.get1(), xcfaLabel);
				if(globalState instanceof PredState) {
					final Set<Expr<BoolType>> preds = new LinkedHashSet<>(((PredState) globalState).getPreds());
					preds.add(Eq(dataflow.getRef(), store.get2().getRef()));
					newState = fromParams(unsafe, currentProcess, currentLoc, backlog, threadLookup, (S)PredState.of(preds), And(invariant, Eq(dataflow.getRef(), store.get2().getRef())), this.revisitableLoads, this.stores, eqPrec, duplicate, counter, newLastPo);
				} else {
					newState = fromParams(unsafe, currentProcess, currentLoc, backlog, threadLookup, globalState, And(invariant, Eq(dataflow.getRef(), store.get2().getRef())), this.revisitableLoads, this.stores, eqPrec, duplicate, counter, newLastPo);
				}
				newStates.add(newState);
			}

			Map<VarDecl<?>, List<Tuple2<XcfaLabel.LoadXcfaLabel<?>, ConstDecl<?>>>> newLoads = new LinkedHashMap<>();
			revisitableLoads.forEach((varDecl, tuple2s) -> newLoads.put(varDecl, new ArrayList<>(tuple2s)));
			newLoads.putIfAbsent(((XcfaLabel.LoadXcfaLabel<?>) xcfaLabel).getGlobal(), new ArrayList<>());
			newLoads.get(((XcfaLabel.LoadXcfaLabel<?>) xcfaLabel).getGlobal()).add(Tuple2.of((XcfaLabel.LoadXcfaLabel<?>) xcfaLabel, dataflow));
			final XcfaDeclarativeState<S> newState = fromParams(unsafe, currentProcess, currentLoc, backlog, threadLookup, globalState, invariant, newLoads, this.stores, eqPrec, newMemoryModelBuilder, counter, newLastPo);
			newStates.add(newState);
			return newStates;
		} else if (xcfaLabel instanceof XcfaLabel.StoreXcfaLabel) {
			Map<VarDecl<?>, List<Tuple2<XcfaLabel.StoreXcfaLabel<?>, ConstDecl<?>>>> newStores = new LinkedHashMap<>();
			stores.forEach((varDecl, tuple2s) -> newStores.put(varDecl, new ArrayList<>(tuple2s)));

			newMemoryModelBuilder.addProgramLoc(((XcfaLabel.StoreXcfaLabel<?>) xcfaLabel).getGlobal());
			newMemoryModelBuilder.addWriteProgramLoc(xcfaLabel, currentProcess, ((XcfaLabel.StoreXcfaLabel<?>) xcfaLabel).getGlobal());
			final ConstDecl<?> dataflow = Const("ARGdataflowW" + counter++, ((XcfaLabel.StoreXcfaLabel<?>) xcfaLabel).getLocal().getType());
			Expr<BoolType> invariant = And(this.invariant, Eq(dataflow.getRef(), ((XcfaLabel.StoreXcfaLabel<?>) xcfaLabel).getLocal().getRef()));

			List<Expr<BoolType>> eqPrec = new ArrayList<>(this.eqPrec);
			eqPrec.add(Eq(dataflow.getRef(), ((XcfaLabel.StoreXcfaLabel<?>) xcfaLabel).getLocal().getRef()));
			newMemoryModelBuilder.addPoEdge(newLastPo, xcfaLabel);
			newLastPo = xcfaLabel;

			newStores.putIfAbsent(((XcfaLabel.StoreXcfaLabel<?>) xcfaLabel).getGlobal(), new ArrayList<>());
			newStores.get(((XcfaLabel.StoreXcfaLabel<?>) xcfaLabel).getGlobal()).add(Tuple2.of((XcfaLabel.StoreXcfaLabel<?>) xcfaLabel, dataflow));

			final List<Tuple2<XcfaLabel.LoadXcfaLabel<?>, ConstDecl<?>>> revisitableLoads = this.revisitableLoads.get(((XcfaLabel.StoreXcfaLabel<?>) xcfaLabel).getGlobal());
			List<XcfaDeclarativeState<S>> newStates = new ArrayList<>();
			if (revisitableLoads != null && revisitableLoads.size() > 0) {
				for (long i = 0; i < (1L << revisitableLoads.size()); i++) { // every subset (binary counting, bit match means choosing the element)
					Collection<Tuple2<XcfaLabel.LoadXcfaLabel<?>, ConstDecl<?>>> chosenLoads = new LinkedHashSet<>();
					List<Expr<BoolType>> newInvariant = new ArrayList<>();
					final MemoryModelBuilder duplicate = newMemoryModelBuilder.duplicate();

					for (int i1 = 0; i1 < revisitableLoads.size(); i1++) {
						if ((i & (1L << i1)) > 0) {
							chosenLoads.add(revisitableLoads.get(i1));
							newInvariant.add(Eq(dataflow.getRef(), revisitableLoads.get(i1).get2().getRef()));
							duplicate.addRfEdge(xcfaLabel, revisitableLoads.get(i1).get1());
						}
					}
					Map<VarDecl<?>, List<Tuple2<XcfaLabel.LoadXcfaLabel<?>, ConstDecl<?>>>> newLoads = new LinkedHashMap<>();
					this.revisitableLoads.forEach((varDecl, tuple2s) -> newLoads.put(varDecl, new ArrayList<>(tuple2s.stream().filter(objects -> !chosenLoads.contains(objects)).collect(Collectors.toList()))));
					final XcfaDeclarativeState<S> newState;
					if(globalState instanceof PredState) {
						final Set<Expr<BoolType>> preds = new LinkedHashSet<>(((PredState) globalState).getPreds());
						preds.add(And(newInvariant));
						newInvariant.add(invariant);
						newState = fromParams(unsafe, currentProcess, currentLoc, backlog, threadLookup, (S)PredState.of(preds), And(newInvariant), newLoads, newStores, eqPrec, newMemoryModelBuilder, counter, newLastPo);
					} else {
						newInvariant.add(invariant);
						newState = fromParams(unsafe, currentProcess, currentLoc, backlog, threadLookup, globalState, And(newInvariant), newLoads, newStores, eqPrec, newMemoryModelBuilder, counter, newLastPo);
					}
					newStates.add(newState);
				}
			} else {
				final XcfaDeclarativeState<S> newState = fromParams(unsafe, currentProcess, currentLoc, backlog, threadLookup, globalState, invariant, this.revisitableLoads, newStores, eqPrec, newMemoryModelBuilder, counter, newLastPo);
				newStates.add(newState);
			}
			return newStates;

		} else {
			throw new UnsupportedOperationException("Label type not recognized: " + xcfaLabel);
		}
	}

	public XcfaDeclarativeState<S> addInvariant(final Expr<BoolType> invariant) {
		return fromParams(unsafe, currentProcess, currentLoc, backlog, threadLookup, globalState, And(this.invariant, invariant), revisitableLoads, stores, eqPrec, memoryModelBuilder.duplicate(), counter, lastPo);
	}

	public XcfaDeclarativeState<S> setInvariant(final Expr<BoolType> invariant) {
		return fromParams(unsafe, currentProcess, currentLoc, backlog, threadLookup, globalState, invariant, revisitableLoads, stores, eqPrec, memoryModelBuilder.duplicate(), counter, lastPo);
	}

	@Override
	public String toString() {
		return "XcfaDeclarativeState{" +
				"unsafe=" + unsafe +
				", currentLoc=" + currentLoc +
				", invariant=" + invariant +
				", globalState=" + globalState +
				", revisitableLoads=" + revisitableLoads.values().stream().map(v -> v.size()).collect(Collectors.toList()) +
				", backlog=" + backlog.size() +
//				", isBottom=" +isBottom() +
				'}';
	}

	public boolean isUnsafe() {
		return unsafe;
	}

	public Integer getCurrentProcess() {
		return currentProcess;
	}

	public List<Expr<BoolType>> getEqPrec() {
		return eqPrec;
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		XcfaDeclarativeState<?> that = (XcfaDeclarativeState<?>) o;
		return currentProcess.equals(that.currentProcess) && Objects.equals(currentLoc, that.currentLoc) && backlog.size() == that.backlog.size() && globalState.equals(that.globalState) && revisitableLoads.equals(that.revisitableLoads) && stores.equals(that.stores) && Objects.equals(invariant, that.invariant);
	}

	@Override
	public int hashCode() {
		return Objects.hash(currentProcess, currentLoc, backlog.size(), globalState, invariant, revisitableLoads, stores);
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
