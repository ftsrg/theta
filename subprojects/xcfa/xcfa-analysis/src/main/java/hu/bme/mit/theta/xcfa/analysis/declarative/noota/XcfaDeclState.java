package hu.bme.mit.theta.xcfa.analysis.declarative.noota;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.cat.solver.DatalogOnlyMemoryModelBuilder;
import hu.bme.mit.theta.cat.solver.MemoryModel;
import hu.bme.mit.theta.cat.solver.MemoryModelBuilder;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.Tuple4;
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
import java.util.Optional;
import java.util.stream.Collectors;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;

public class XcfaDeclState<S extends ExprState> implements ExprState {
	private final S state;
	private final Expr<BoolType> invariant;
	private final Integer currentProcess;
	private final Map<Integer, Tuple4<XcfaLocation, Object, Optional<VarDecl<?>>, Optional<Object>>> processes; // process -> tup(loc, lastPo, isBlocked_loc, isAtomic)
	private final Map<VarDecl<?>, Integer> processLookup;
	private final Map<Integer, XcfaProcess> processIndexLookup;
	private final Map<VarDecl<?>, List<Tuple2<Object, VarDecl<?>>>> stores;
	private final Map<VarDecl<?>, List<Tuple2<Object, XcfaLabel.LoadXcfaLabel<?>>>> revisitableLoads;
	private final Map<VarDecl<?>, Integer> loadsSoFar;
	private final Map<Object, Integer> blockedBy;
	private final MemoryModelBuilder memoryModelBuilder;

	public XcfaDeclState(final S state, Expr<BoolType> invariant, final Integer currentProcess,
						 final Map<Integer, Tuple4<XcfaLocation, Object, Optional<VarDecl<?>>, Optional<Object>>> processes,
						 final Map<VarDecl<?>, Integer> processLookup, final Map<Integer, XcfaProcess> processIndexLookup,
						 final Map<VarDecl<?>, List<Tuple2<Object, VarDecl<?>>>> stores,
						 final Map<VarDecl<?>, List<Tuple2<Object, XcfaLabel.LoadXcfaLabel<?>>>> revisitableLoads,
						 final Map<VarDecl<?>, Integer> loadsSoFar, final Map<Object, Integer> blockedBy, final MemoryModelBuilder memoryModelBuilder) {
		this.state = state;
		this.invariant = invariant;
		this.currentProcess = currentProcess;
		this.processes = processes;
		this.processLookup = processLookup;
		this.processIndexLookup = processIndexLookup;
		this.stores = stores;
		this.revisitableLoads = revisitableLoads;
		this.loadsSoFar = loadsSoFar;
		this.blockedBy = blockedBy;
		this.memoryModelBuilder = memoryModelBuilder;
	}

	public static <S extends ExprState> XcfaDeclState<S> init(XcfaLocation initLoc, MemoryModel memoryModel, S s) {
		final MemoryModelBuilder memoryModelBuilder = DatalogOnlyMemoryModelBuilder.create(memoryModel);
		final Object firstPo = new Object();
		memoryModelBuilder.addProgramLoc(firstPo);
		return new XcfaDeclState<>(s, True(), 0, Map.of(0, Tuple4.of(initLoc, firstPo, Optional.empty(), Optional.empty())),
				Map.of(), Map.of(0, initLoc.getParent().getParent()), Map.of(), Map.of(), Map.of(), Map.of(), memoryModelBuilder);
	}

	public XcfaDeclState<S> setInvariant(final Expr<BoolType> invariant) {
		return new XcfaDeclState<>(getState(), invariant, getCurrentProcess(), getProcesses(), getProcessLookup(), getProcessIndexLookup(), getStores(), getRevisitableLoads(), getLoadsSoFar(), getBlockedBy(), getMemoryModelBuilder());
	}

	public XcfaDeclState<S> atomicBegin() {
		if (this.processes.get(currentProcess).get3().isPresent()) return this;

		final MemoryModelBuilder newMemoryModelBuilder = memoryModelBuilder.duplicate();
		final Object amoHelper = new Object();
		newMemoryModelBuilder.addProgramLoc(amoHelper);

		final Map<Integer, Tuple4<XcfaLocation, Object, Optional<VarDecl<?>>, Optional<Object>>> newProcesses = new LinkedHashMap<>();
		this.processes.forEach((process, objects) -> {
			if (process.equals(currentProcess)) {
				newProcesses.put(process, Tuple4.of(objects.get1(), objects.get2(), objects.get3(), Optional.of(amoHelper)));
			} else {
				newProcesses.put(process, objects);
			}
		});
		return new XcfaDeclState<>(getState(), invariant, getCurrentProcess(), newProcesses, getProcessLookup(), getProcessIndexLookup(), getStores(), getRevisitableLoads(), getLoadsSoFar(), getBlockedBy(), newMemoryModelBuilder);
	}

	public XcfaDeclState<S> atomicEnd() {
		if (this.processes.get(currentProcess).get3().isEmpty()) return this;

		final MemoryModelBuilder newMemoryModelBuilder = memoryModelBuilder.duplicate();

		final Map<Integer, Tuple4<XcfaLocation, Object, Optional<VarDecl<?>>, Optional<Object>>> newProcesses = new LinkedHashMap<>();
		this.processes.forEach((process, objects) -> {
			if (process.equals(currentProcess)) {
				newProcesses.put(process, Tuple4.of(objects.get1(), objects.get2(), objects.get3(), Optional.empty()));
			} else {
				newProcesses.put(process, objects);
			}
		});
		return new XcfaDeclState<>(getState(), invariant, getCurrentProcess(), newProcesses, getProcessLookup(), getProcessIndexLookup(), getStores(), getRevisitableLoads(), getLoadsSoFar(), getBlockedBy(), newMemoryModelBuilder);
	}

	public XcfaDeclState<S> startThread(final XcfaLabel.StartThreadXcfaLabel xcfaLabel) {
		final XcfaProcess process = xcfaLabel.getProcess();

		final MemoryModelBuilder newMemoryModelBuilder = memoryModelBuilder.duplicate();
		final Object threadStart = new Object();
		newMemoryModelBuilder.addProgramLoc(threadStart);
		newMemoryModelBuilder.addPoEdge(this.processes.get(currentProcess).get2(), threadStart);

		final Tuple4<XcfaLocation, Object, Optional<VarDecl<?>>, Optional<Object>> tup =
				Tuple4.of(process.getMainProcedure().getInitLoc(), threadStart, Optional.empty(), Optional.empty());

		final Map<Integer, Tuple4<XcfaLocation, Object, Optional<VarDecl<?>>, Optional<Object>>> newProcesses = new LinkedHashMap<>(processes);
		newProcesses.put(processes.size(), tup);

		final Map<VarDecl<?>, Integer> newProcessLookup = new LinkedHashMap<>(processLookup);
		newProcessLookup.put(xcfaLabel.getKey(), processes.size());

		final Map<Integer, XcfaProcess> newProcessIndexLookup = new LinkedHashMap<>(processIndexLookup);
		newProcessIndexLookup.put(processes.size(), process);

		return new XcfaDeclState<>(getState(), invariant, getCurrentProcess(), newProcesses, newProcessLookup, newProcessIndexLookup, getStores(), getRevisitableLoads(), getLoadsSoFar(), getBlockedBy(), newMemoryModelBuilder);
	}

	public XcfaDeclState<S> joinThread(final XcfaLabel.JoinThreadXcfaLabel xcfaLabel) {
		final Integer process = this.processLookup.get(xcfaLabel.getKey());

		final MemoryModelBuilder newMemoryModelBuilder = memoryModelBuilder.duplicate();
		final Object threadEnd = processIndexLookup.get(process); // End is marked by the process itself
		newMemoryModelBuilder.addPoEdge(threadEnd, this.processes.get(currentProcess).get2());

		return new XcfaDeclState<>(getState(), invariant, getCurrentProcess(), getProcesses(), getProcessLookup(), getProcessIndexLookup(), getStores(), getRevisitableLoads(), getLoadsSoFar(), getBlockedBy(), newMemoryModelBuilder);
	}

	public XcfaDeclState<S> addRead(final XcfaLabel.LoadXcfaLabel<?> loadXcfaLabel, final Object load) {
		final ImmutableMap.Builder<VarDecl<?>, List<Tuple2<Object, XcfaLabel.LoadXcfaLabel<?>>>> newRevisitableLoadBuilder = ImmutableMap.builder();
		boolean absent = true;
		for (Map.Entry<VarDecl<?>, List<Tuple2<Object, XcfaLabel.LoadXcfaLabel<?>>>> entry : revisitableLoads.entrySet()) {
			VarDecl<?> varDecl = entry.getKey();
			List<Tuple2<Object, XcfaLabel.LoadXcfaLabel<?>>> tuple2s = entry.getValue();
			if (varDecl.equals(loadXcfaLabel.getGlobal())) {
				absent = false;
				tuple2s = new ArrayList<>(tuple2s);
				tuple2s.add(Tuple2.of(load, loadXcfaLabel));
			}
			newRevisitableLoadBuilder.put(varDecl, ImmutableList.copyOf(tuple2s));
		}
		if(absent) newRevisitableLoadBuilder.put(loadXcfaLabel.getGlobal(), List.of(Tuple2.of(load, loadXcfaLabel)));

		Map<VarDecl<?>, Integer> newLoadsSoFar = new LinkedHashMap<>(loadsSoFar);
		newLoadsSoFar.putIfAbsent(loadXcfaLabel.getGlobal(), newLoadsSoFar.getOrDefault(loadXcfaLabel.getGlobal(), 0) + 1);


		final MemoryModelBuilder newMemoryModelBuilder = memoryModelBuilder.duplicate();
		newMemoryModelBuilder.addProgramLoc(currentProcess);
		newMemoryModelBuilder.addProgramLoc(loadXcfaLabel.getGlobal());
		newMemoryModelBuilder.addReadProgramLoc(load, currentProcess, loadXcfaLabel.getGlobal());
		newMemoryModelBuilder.addPoEdge(this.processes.get(currentProcess).get2(), load);
		if(this.processes.get(currentProcess).get4().isPresent()) {
			newMemoryModelBuilder.addAmo(load, this.processes.get(currentProcess).get4().get());
		}

		final Map<Integer, Tuple4<XcfaLocation, Object, Optional<VarDecl<?>>, Optional<Object>>> newProcesses = new LinkedHashMap<>();
		this.processes.forEach((process, objects) -> {
			if (process.equals(currentProcess)) {
				newProcesses.put(process, Tuple4.of(objects.get1(), load, Optional.of(loadXcfaLabel.getLocal()), objects.get4()));
			} else {
				newProcesses.put(process, objects);
			}
		});

		final LinkedHashMap<Object, Integer> newBlockedBy = new LinkedHashMap<>(blockedBy);
		newBlockedBy.put(load, currentProcess);

		return new XcfaDeclState<>(getState(), invariant, getCurrentProcess(), newProcesses, getProcessLookup(), getProcessIndexLookup(), getStores(), newRevisitableLoadBuilder.build(), newLoadsSoFar, newBlockedBy, newMemoryModelBuilder);
	}

	public XcfaDeclState<S> addRead(final XcfaLabel.LoadXcfaLabel<?> loadXcfaLabel, final Object load, final Object readsFrom) {
		if(readsFrom == null) return addRead(loadXcfaLabel, load);

		final MemoryModelBuilder newMemoryModelBuilder = memoryModelBuilder.duplicate();
		newMemoryModelBuilder.addProgramLoc(currentProcess);
		newMemoryModelBuilder.addProgramLoc(loadXcfaLabel.getGlobal());
		newMemoryModelBuilder.addReadProgramLoc(load, currentProcess, loadXcfaLabel.getGlobal());
		newMemoryModelBuilder.addPoEdge(this.processes.get(currentProcess).get2(), load);
		newMemoryModelBuilder.addRfEdge(readsFrom, load);
		if(this.processes.get(currentProcess).get4().isPresent()) {
			newMemoryModelBuilder.addAmo(load, this.processes.get(currentProcess).get4().get());
		}

		final Map<Integer, Tuple4<XcfaLocation, Object, Optional<VarDecl<?>>, Optional<Object>>> newProcesses = new LinkedHashMap<>();
		this.processes.forEach((process, objects) -> {
			if (process.equals(currentProcess)) {
				newProcesses.put(process, Tuple4.of(objects.get1(), load, objects.get3(), objects.get4()));
			} else {
				newProcesses.put(process, objects);
			}
		});


		Map<VarDecl<?>, Integer> newLoadsSoFar = new LinkedHashMap<>(loadsSoFar);
		newLoadsSoFar.putIfAbsent(loadXcfaLabel.getGlobal(), newLoadsSoFar.getOrDefault(loadXcfaLabel.getGlobal(), 0) + 1);

		return new XcfaDeclState<>(getState(), invariant, getCurrentProcess(), newProcesses, getProcessLookup(), getProcessIndexLookup(), getStores(), getRevisitableLoads(), newLoadsSoFar, getBlockedBy(), newMemoryModelBuilder);
	}

	public XcfaDeclState<S> addStore(final XcfaLabel.StoreXcfaLabel<?> storeXcfaLabel, final Object store, final VarDecl<?> valueStore, final Collection<Tuple2<Object, XcfaLabel.LoadXcfaLabel<?>>> writesTo) {
		final ImmutableMap.Builder<VarDecl<?>, List<Tuple2<Object, XcfaLabel.LoadXcfaLabel<?>>>> newRevisitableLoadBuilder = ImmutableMap.builder();
		for (Map.Entry<VarDecl<?>, List<Tuple2<Object, XcfaLabel.LoadXcfaLabel<?>>>> entry : revisitableLoads.entrySet()) {
			VarDecl<?> varDecl = entry.getKey();
			List<Tuple2<Object, XcfaLabel.LoadXcfaLabel<?>>> tuple2s = entry.getValue();
			if (varDecl.equals(storeXcfaLabel.getGlobal())) {
				tuple2s = new ArrayList<>(tuple2s);
				tuple2s.removeAll(writesTo);
			}
			newRevisitableLoadBuilder.put(varDecl, ImmutableList.copyOf(tuple2s));
		}

		final ImmutableMap.Builder<VarDecl<?>, List<Tuple2<Object, VarDecl<?>>>> newStoresBuilder = ImmutableMap.builder();
		boolean absent = true;
		for (Map.Entry<VarDecl<?>, List<Tuple2<Object, VarDecl<?>>>> entry : stores.entrySet()) {
			VarDecl<?> varDecl = entry.getKey();
			List<Tuple2<Object, VarDecl<?>>> tuple2s = entry.getValue();
			if (varDecl.equals(storeXcfaLabel.getGlobal())) {
				absent = false;
				tuple2s = new ArrayList<>(tuple2s);
				tuple2s.add(Tuple2.of(store, valueStore));
			}
			newStoresBuilder.put(varDecl, ImmutableList.copyOf(tuple2s));
		}
		if(absent) newStoresBuilder.put(storeXcfaLabel.getGlobal(), List.of(Tuple2.of(store, valueStore)));

		final MemoryModelBuilder newMemoryModelBuilder = memoryModelBuilder.duplicate();
		newMemoryModelBuilder.addProgramLoc(currentProcess);
		newMemoryModelBuilder.addProgramLoc(storeXcfaLabel.getGlobal());
		newMemoryModelBuilder.addWriteProgramLoc(store, currentProcess, storeXcfaLabel.getGlobal());
		newMemoryModelBuilder.addPoEdge(this.processes.get(currentProcess).get2(), store);
		if(this.processes.get(currentProcess).get4().isPresent()) {
			newMemoryModelBuilder.addAmo(store, this.processes.get(currentProcess).get4().get());
		}
		Collection<Integer> blockedProcesses = new LinkedHashSet<>();
		final LinkedHashMap<Object, Integer> newBlockedBy = new LinkedHashMap<>(blockedBy);
		for (Tuple2<Object, XcfaLabel.LoadXcfaLabel<?>> objects : writesTo) {
			newMemoryModelBuilder.addRfEdge(store, objects.get1());
			blockedProcesses.add(blockedBy.get(objects.get1()));
			newBlockedBy.remove(objects.get1());
		}

		final Map<Integer, Tuple4<XcfaLocation, Object, Optional<VarDecl<?>>, Optional<Object>>> newProcesses = new LinkedHashMap<>();
		this.processes.forEach((process, objects) -> {
			if (currentProcess.equals(process)) {
				newProcesses.put(process, Tuple4.of(objects.get1(), store, objects.get3(), objects.get4()));
			} else if (blockedProcesses.contains(process)) {
				newProcesses.put(process, Tuple4.of(objects.get1(), objects.get2(), Optional.empty(), objects.get4()));
			} else {
				newProcesses.put(process, objects);
			}
		});

		return new XcfaDeclState<>(getState(), invariant, getCurrentProcess(), newProcesses, getProcessLookup(), getProcessIndexLookup(), newStoresBuilder.build(), newRevisitableLoadBuilder.build(), getLoadsSoFar(), newBlockedBy, newMemoryModelBuilder);
	}

	public XcfaDeclState<S> addFence(final XcfaLabel.FenceXcfaLabel fenceXcfaLabel) {
		final MemoryModelBuilder newMemoryModelBuilder = memoryModelBuilder.duplicate();
		final Object fence = new Object();
		newMemoryModelBuilder.addFenceLoc(fence, currentProcess);
		newMemoryModelBuilder.addPoEdge(this.processes.get(currentProcess).get2(), fence);
		if(this.processes.get(currentProcess).get4().isPresent()) {
			newMemoryModelBuilder.addAmo(fence, this.processes.get(currentProcess).get4().get());
		}

		final Map<Integer, Tuple4<XcfaLocation, Object, Optional<VarDecl<?>>, Optional<Object>>> newProcesses = new LinkedHashMap<>();
		this.processes.forEach((process, objects) -> {
			if (process.equals(currentProcess)) {
				newProcesses.put(process, Tuple4.of(objects.get1(), fence, objects.get3(), objects.get4()));
			} else {
				newProcesses.put(process, objects);
			}
		});

		return new XcfaDeclState<>(getState(), invariant, getCurrentProcess(), newProcesses, getProcessLookup(), getProcessIndexLookup(), getStores(), getRevisitableLoads(), getLoadsSoFar(), getBlockedBy(), newMemoryModelBuilder);
	}

	public XcfaDeclState<S> changeThread(final Integer changeTo) {
		return new XcfaDeclState<>(getState(), invariant, changeTo, getProcesses(), getProcessLookup(), getProcessIndexLookup(), getStores(), getRevisitableLoads(), getLoadsSoFar(), getBlockedBy(), getMemoryModelBuilder());
	}

	public XcfaDeclState<S> newState(final S newState) {
		return new XcfaDeclState<>(newState, invariant, getCurrentProcess(), getProcesses(), getProcessLookup(), getProcessIndexLookup(), getStores(), getRevisitableLoads(), getLoadsSoFar(), getBlockedBy(), getMemoryModelBuilder());
	}

	public XcfaDeclState<S> advance(final XcfaLocation advanceTo) {
		final Map<Integer, Tuple4<XcfaLocation, Object, Optional<VarDecl<?>>, Optional<Object>>> newProcesses = new LinkedHashMap<>();
		this.processes.forEach((process, objects) -> {
			if (currentProcess.equals(process)) {
				newProcesses.put(process, Tuple4.of(advanceTo, objects.get2(), objects.get3(), objects.get4()));
			} else {
				newProcesses.put(process, objects);
			}
		});
		return new XcfaDeclState<>(getState(), invariant, getCurrentProcess(), newProcesses, getProcessLookup(), getProcessIndexLookup(), getStores(), getRevisitableLoads(), getLoadsSoFar(), getBlockedBy(), getMemoryModelBuilder());
	}

	public boolean isUnsafe() {
		return processes.get(currentProcess).get1().isErrorLoc();
	}

	@Override
	public boolean isBottom() {
		return state.isBottom() || !memoryModelBuilder.check();
	}

	@Override
	public Expr<BoolType> toExpr() {
		return And(state.toExpr(), invariant);
	}

	public S getState() {
		return state;
	}

	public Integer getCurrentProcess() {
		return currentProcess;
	}

	public Map<Integer, Tuple4<XcfaLocation, Object, Optional<VarDecl<?>>, Optional<Object>>> getProcesses() {
		return ImmutableMap.copyOf(processes);
	}

	public Map<VarDecl<?>, Integer> getProcessLookup() {
		return ImmutableMap.copyOf(processLookup);
	}

	public Map<Integer, XcfaProcess> getProcessIndexLookup() {
		return Map.copyOf(processIndexLookup);
	}

	public Map<Object, Integer> getBlockedBy() {
		return ImmutableMap.copyOf(blockedBy);
	}

	public Map<VarDecl<?>, List<Tuple2<Object, VarDecl<?>>>> getStores() {
		final ImmutableMap.Builder<VarDecl<?>, List<Tuple2<Object, VarDecl<?>>>> builder = ImmutableMap.builder();
		stores.forEach((varDecl, tuple2s) -> builder.put(varDecl, ImmutableList.copyOf(tuple2s)));
		return builder.build();
	}

	public Map<VarDecl<?>, List<Tuple2<Object, XcfaLabel.LoadXcfaLabel<?>>>> getRevisitableLoads() {
		final ImmutableMap.Builder<VarDecl<?>, List<Tuple2<Object, XcfaLabel.LoadXcfaLabel<?>>>> builder = ImmutableMap.builder();
		revisitableLoads.forEach((varDecl, tuple2s) -> builder.put(varDecl, ImmutableList.copyOf(tuple2s)));
		return builder.build();
	}

	public Map<VarDecl<?>, Integer> getLoadsSoFar() {
		return Map.copyOf(loadsSoFar);
	}

	public MemoryModelBuilder getMemoryModelBuilder() {
		return memoryModelBuilder.duplicate();
	}

	@Override
	public String toString() {
		return "XcfaDeclState{" +
				"state=" + state +
				", currentProcess=" + currentProcess +
//				", processes=" + processes.entrySet().stream().map(e -> Map.entry(e.getKey(), Tuple2.of(e.getValue().get1(), e.getValue().get2()))).collect(Collectors.toMap(Map.Entry::getKey, Map.Entry::getValue)) +
				", processes=" + processes.size() +
				", stores=" + stores.entrySet().stream().map(e -> Map.entry(e.getKey(), e.getValue().size())).collect(Collectors.toMap(Map.Entry::getKey, Map.Entry::getValue)) +
				", revisitableLoads=" + revisitableLoads.entrySet().stream().map(e -> Map.entry(e.getKey(), e.getValue().stream().map(Tuple2::get2).collect(Collectors.toList()))).collect(Collectors.toMap(Map.Entry::getKey, Map.Entry::getValue)) +
				", blockedBy=" + blockedBy.values() +
				'}';
	}
}
