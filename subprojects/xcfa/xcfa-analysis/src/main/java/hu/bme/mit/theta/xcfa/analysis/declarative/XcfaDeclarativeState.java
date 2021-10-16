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
import hu.bme.mit.theta.analysis.pred.PredState;
import hu.bme.mit.theta.cat.models.CoherenceMemory;
import hu.bme.mit.theta.cat.solver.BoolSmtMemoryModelBuilder;
import hu.bme.mit.theta.cat.solver.MemoryModelBuilder;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.MutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaProcess;
import hu.bme.mit.theta.xcfa.model.utils.XcfaLabelVarReplacer;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.decl.Decls.Const;
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
	private final Map<VarDecl<?>, List<Tuple2<XcfaLabel.LoadXcfaLabel<?>, Tuple2<S, ConstDecl<?>>>>> loads;
	private final Map<VarDecl<?>, List<Tuple2<XcfaLabel.StoreXcfaLabel<?>, Tuple2<S, ConstDecl<?>>>>> stores;
	private final MemoryModelBuilder memoryModelBuilder;
	private final Object lastPo;

	private XcfaDeclarativeState(final boolean unsafe, final Integer currentProcess, final XcfaLocation currentLoc, final Map<Integer, XcfaProcess> backlog, final Map<VarDecl<?>, Integer> threadLookup, final S globalState, Expr<BoolType> invariant, final Map<VarDecl<?>, List<Tuple2<XcfaLabel.LoadXcfaLabel<?>, Tuple2<S, ConstDecl<?>>>>> loads, final Map<VarDecl<?>, List<Tuple2<XcfaLabel.StoreXcfaLabel<?>, Tuple2<S, ConstDecl<?>>>>> stores, final MemoryModelBuilder memoryModelBuilder, final Object lastPo) {
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
		if(lastPo == null) {
			this.lastPo = new Object();
			memoryModelBuilder.addProgramLoc(this.lastPo);
		} else {
			this.lastPo = lastPo;
		}
	}

	public static <S extends ExprState> XcfaDeclarativeState<S> fromParams(final boolean unsafe, final Integer currentProcess, final XcfaLocation currentLoc, final Map<Integer, XcfaProcess> backlog, final Map<VarDecl<?>, Integer> threadLookup, final S globalState, final Expr<BoolType> invariant, final Map<VarDecl<?>, List<Tuple2<XcfaLabel.LoadXcfaLabel<?>, Tuple2<S, ConstDecl<?>>>>> loads, final Map<VarDecl<?>, List<Tuple2<XcfaLabel.StoreXcfaLabel<?>, Tuple2<S, ConstDecl<?>>>>> stores, final MemoryModelBuilder memoryModelBuilder, final Object lastPo) {
		return new XcfaDeclarativeState<S>(unsafe, currentProcess, currentLoc, backlog, threadLookup, globalState, invariant, loads, stores, memoryModelBuilder, lastPo);
	}

	public static <S extends ExprState> XcfaDeclarativeState<S> create(final XcfaLocation currentLoc, final S globalState) {
		return fromParams(currentLoc.isErrorLoc(), -1, currentLoc, Map.of(), Map.of(), globalState, True(), Map.of(), Map.of(), BoolSmtMemoryModelBuilder.create(new CoherenceMemory()), null);
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
			return true;
//			List<Tuple2<?, ConstDecl<?>>> writes = new ArrayList<>();
//			List<Tuple2<?, ConstDecl<?>>> reads = new ArrayList<>();
//			Solver solver = Z3SolverFactory.getInstance().createSolver();
//
//			loads.forEach((varDecl, tuple2s) -> {
//				for (Tuple2<XcfaLabel.LoadXcfaLabel<?>, Tuple2<S, ConstDecl<?>>> loadTuple : tuple2s) {
//					Expr<BoolType> expr = False();
//					for (Tuple2<XcfaLabel.StoreXcfaLabel<?>, Tuple2<S, ConstDecl<?>>> storeTuple : stores.get(varDecl)) {
//						expr = Or(expr, Eq(loadTuple.get2().get2().getRef(), storeTuple.get2().get2().getRef()));
//					}
//					solver.add(expr);
//					solver.add(loadTuple.get2().get1().toExpr());
//				}
//			});
//			stores.forEach((varDecl, tuple2s) -> tuple2s.forEach(objects -> solver.add(objects.get2().get1().toExpr())));

//			stores.forEach((varDecl, tuple2s) -> tuple2s.forEach(objects -> {
//				writes.add(Tuple2.of(objects.get1(), objects.get2().get2()));
//				solver.add(objects.get2().get1().toExpr());
//			}));
//			loads.forEach((varDecl, tuple2s) -> tuple2s.forEach(objects -> {
//				reads.add(Tuple2.of(objects.get1(), objects.get2().get2()));
//				solver.add(objects.get2().get1().toExpr());
//			}));
//			solver.add(memoryModelBuilder.addConstraints(writes, reads));
//			return solver.check().isSat();
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

	public Map<VarDecl<?>, List<Tuple2<XcfaLabel.LoadXcfaLabel<?>, Tuple2<S, ConstDecl<?>>>>> getLoads() {
		return loads;
	}

	public Map<VarDecl<?>, List<Tuple2<XcfaLabel.StoreXcfaLabel<?>, Tuple2<S, ConstDecl<?>>>>> getStores() {
		return stores;
	}

	public XcfaDeclarativeState<S> atomicbegin(final Boolean atomicBegin) {
		return fromParams(unsafe, currentProcess, currentLoc, backlog, threadLookup, globalState, invariant, loads, stores, memoryModelBuilder.duplicate(), lastPo);
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
		return fromParams(unsafe, currentProcess, currentLoc, newBacklog, newThreadLookup, globalState, invariant, loads, stores, newMemoryModelBuilder, lastPo);
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
			return fromParams(unsafe, currentProcess, currentLoc, backlog, threadLookup, globalState, invariant,  loads, stores, newMemoryModelBuilder, newLastPo);
		}
		return fromParams(unsafe, currentProcess, currentLoc, backlog, threadLookup, globalState, invariant,  loads, stores, newMemoryModelBuilder, lastPo);
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
		return fromParams(unsafe || action.getTarget().isErrorLoc(), process, action.getTarget(), newBackLog, threadLookup, succState, invariant,  loads, stores, newMemoryModelBuilder, newLastPo);
	}

	public XcfaDeclarativeState<S> memory(final List<XcfaLabel> memory) {
		Map<VarDecl<?>, List<Tuple2<XcfaLabel.StoreXcfaLabel<?>, Tuple2<S, ConstDecl<?>>>>> newStores = new LinkedHashMap<>();
		stores.forEach((varDecl, tuple2s) -> newStores.put(varDecl, new ArrayList<>(tuple2s)));
		Map<VarDecl<?>, List<Tuple2<XcfaLabel.LoadXcfaLabel<?>, Tuple2<S, ConstDecl<?>>>>> newLoads = new LinkedHashMap<>();
		loads.forEach((varDecl, tuple2s) -> newLoads.put(varDecl, new ArrayList<>(tuple2s)));
		final MemoryModelBuilder newMemoryModelBuilder = memoryModelBuilder.duplicate();
		Object newLastPo = lastPo;
		for (XcfaLabel xcfaLabel : memory) {
			newMemoryModelBuilder.addProgramLoc(currentProcess);
			if(xcfaLabel instanceof XcfaLabel.LoadXcfaLabel) {
				newMemoryModelBuilder.addProgramLoc(((XcfaLabel.LoadXcfaLabel<?>) xcfaLabel).getGlobal());
				newMemoryModelBuilder.addReadProgramLoc(xcfaLabel, currentProcess, ((XcfaLabel.LoadXcfaLabel<?>) xcfaLabel).getGlobal());
				newLoads.putIfAbsent(((XcfaLabel.LoadXcfaLabel<?>) xcfaLabel).getGlobal(), new ArrayList<>());
				newLoads.get(((XcfaLabel.LoadXcfaLabel<?>) xcfaLabel).getGlobal()).add(Tuple2.of((XcfaLabel.LoadXcfaLabel<?>) xcfaLabel, getUniqeState(globalState, ((XcfaLabel.LoadXcfaLabel<?>) xcfaLabel).getLocal())));
			} else if (xcfaLabel instanceof XcfaLabel.StoreXcfaLabel) {
				newMemoryModelBuilder.addProgramLoc(((XcfaLabel.StoreXcfaLabel<?>) xcfaLabel).getGlobal());
				newMemoryModelBuilder.addWriteProgramLoc(xcfaLabel, currentProcess, ((XcfaLabel.StoreXcfaLabel<?>) xcfaLabel).getGlobal());
				newStores.putIfAbsent(((XcfaLabel.StoreXcfaLabel<?>) xcfaLabel).getGlobal(), new ArrayList<>());
				newStores.get(((XcfaLabel.StoreXcfaLabel<?>) xcfaLabel).getGlobal()).add(Tuple2.of((XcfaLabel.StoreXcfaLabel<?>) xcfaLabel, getUniqeState(globalState, ((XcfaLabel.StoreXcfaLabel<?>) xcfaLabel).getLocal())));
			} else if (xcfaLabel instanceof XcfaLabel.FenceXcfaLabel) {
				newMemoryModelBuilder.addFenceLoc(xcfaLabel, currentProcess);
			} else {
				throw new UnsupportedOperationException("Label type not recognized: " + xcfaLabel);
			}
			newMemoryModelBuilder.addPoEdge(newLastPo, xcfaLabel);
			newLastPo = xcfaLabel;
		}
		return fromParams(unsafe, currentProcess, currentLoc, backlog, threadLookup, globalState, invariant,  newLoads, newStores, newMemoryModelBuilder, newLastPo);
	}

	private static int counter = 0;
	private Tuple2<S, ConstDecl<?>> getUniqeState(S globalState, VarDecl<?> local) {
		if(globalState.isBottom()) return Tuple2.of(globalState, Const(local.getName(), local.getType()));
		if(globalState instanceof ExplState) {
			final Valuation val = ((ExplState) globalState).getVal();
			final MutableValuation newVal = new MutableValuation();
			ConstDecl<?> ret=null;
			for (Map.Entry<Decl<?>, LitExpr<?>> entry : val.toMap().entrySet()) {
				Decl<?> decl = entry.getKey();
				LitExpr<?> litExpr = entry.getValue();
				final ConstDecl<?> var = Const(decl.getName() + counter++, decl.getType());
				if (decl == local) ret = var;
				newVal.put(var, litExpr);
			}
			if(ret != null) {
				return Tuple2.of((S) ExplState.of(newVal), ret);
			} else {
				return Tuple2.of((S) ExplState.top(), ret);
			}
		} else if (globalState instanceof PredState) {
			Map<VarDecl<?>, ConstDecl<?>> varLut = new LinkedHashMap<>();
			Collection<Expr<BoolType>> newPreds = new ArrayList<>();
			for (Expr<BoolType> pred : ((PredState) globalState).getPreds()) {
				for (VarDecl<?> var : ExprUtils.getVars(pred)) {
					varLut.putIfAbsent(var, Const(var.getName() + counter++, var.getType()));
				}
				newPreds.add(XcfaLabelVarReplacer.replaceVars(pred, varLut));
			}
			if(varLut.containsKey(local)) {
				return Tuple2.of((S)PredState.of(newPreds), varLut.get(local));
			} else {
				return Tuple2.of((S)PredState.of(True()), Const(local.getName(), local.getType()));
			}

		}
		throw new UnsupportedOperationException("State not supported!");
	}

	public XcfaDeclarativeState<S> addInvariant(final Expr<BoolType> invariant) {
		return fromParams(unsafe, currentProcess, currentLoc, backlog, threadLookup, globalState, invariant,  loads, stores, memoryModelBuilder.duplicate(), lastPo);
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
