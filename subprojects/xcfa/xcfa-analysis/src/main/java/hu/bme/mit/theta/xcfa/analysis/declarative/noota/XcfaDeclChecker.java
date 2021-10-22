package hu.bme.mit.theta.xcfa.analysis.declarative.noota;

import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceStatus;
import hu.bme.mit.theta.analysis.expr.refinement.Refutation;
import hu.bme.mit.theta.cat.solver.BoolDatalogMemoryModelBuilder;
import hu.bme.mit.theta.cat.solver.MemoryModel;
import hu.bme.mit.theta.cat.solver.MemoryModelBuilder;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverStatus;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;
import hu.bme.mit.theta.xcfa.analysis.declarative.noota.actions.XcfaDeclAction;
import hu.bme.mit.theta.xcfa.analysis.declarative.noota.actions.XcfaLabelAction;
import hu.bme.mit.theta.xcfa.analysis.declarative.noota.actions.XcfaLoadAction;
import hu.bme.mit.theta.xcfa.analysis.declarative.noota.actions.XcfaSequenceAction;
import hu.bme.mit.theta.xcfa.analysis.declarative.noota.actions.XcfaStoreAction;
import hu.bme.mit.theta.xcfa.analysis.declarative.noota.actions.XcfaThreadChangeAction;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;

public class XcfaDeclChecker<R extends Refutation> implements ExprTraceChecker<R> {
	private final ExprTraceChecker<R> traceChecker;
	private final boolean preCheck;
	private final MemoryModel memoryModel;

	private XcfaDeclChecker(final ExprTraceChecker<R> traceChecker, final boolean preCheck, final MemoryModel memoryModel) {
		this.traceChecker = traceChecker;
		this.preCheck = preCheck;
		this.memoryModel = memoryModel;
	}

	public static <R extends Refutation> XcfaDeclChecker<R> create(final ExprTraceChecker<R> traceChecker, final boolean preCheck, final MemoryModel memoryModel) {
		return new XcfaDeclChecker<R>(traceChecker, preCheck, memoryModel);
	}

	@Override
	public ExprTraceStatus<R> check(Trace<? extends ExprState, ? extends ExprAction> trace) {
//		if(!ArchitectureConfig.multiThreading) {
			if(true) return traceChecker.check(trace);
//		}

		if(preCheck) {
			final ExprTraceStatus<R> check = traceChecker.check(trace);
			if(check.isInfeasible()) return check;
		}

		final MemoryModelBuilder memoryModelBuilder = BoolDatalogMemoryModelBuilder.create(memoryModel, Z3SolverFactory.getInstance().createSolver());
		final Object firstPo = new Object();
		memoryModelBuilder.addProgramLoc(firstPo);

		final List<XcfaDeclAction> actions = (List<XcfaDeclAction>) trace.getActions();
		final XcfaDeclState<?> state0 = (XcfaDeclState<?>) trace.getState(0);
		memoryModelBuilder.addProgramLoc(state0.getCurrentProcess());
		List<Tuple2<?, ConstDecl<?>>> writes = new ArrayList<>();
		List<Tuple2<?, ConstDecl<?>>> reads = new ArrayList<>();
		handleSequenceAction(XcfaSequenceAction.of(actions), state0.getCurrentProcess(), new LinkedHashMap<>(Map.of(state0.getCurrentProcess(), firstPo)), memoryModelBuilder, writes, reads);

		memoryModelBuilder.addConstraints(writes, reads);
		final Collection<Expr<BoolType>> assertions = memoryModelBuilder.getAssertions();

		final List<? extends XcfaDeclState<?>> newStates = trace.getStates().stream().map(exprState -> ((XcfaDeclState<?>) exprState).setInvariant(And(assertions))).collect(Collectors.toList());

		final ExprTraceStatus<R> check = traceChecker.check(Trace.of(newStates, trace.getActions()));
		if(check.isInfeasible()) {
			final R refutation = check.asInfeasible().getRefutation();
		}

		return check;
	}

	private void handleSequenceAction(XcfaSequenceAction action, Integer currentProcess, Map<Integer, Object> pos, MemoryModelBuilder memoryModelBuilder, List<Tuple2<?, ConstDecl<?>>> writes, List<Tuple2<?, ConstDecl<?>>> reads) {
		int counter = 1;
		final Map<VarDecl<?>, Integer> lut = new LinkedHashMap<>();

		List<XcfaDeclAction> actions = new ArrayList<>(action.getActions());
		while (actions.size() > 0) {
			XcfaDeclAction actionAction = actions.get(0);
			actions.remove(0);
			if(actionAction instanceof XcfaSequenceAction) {
				actions.addAll(0, ((XcfaSequenceAction) actionAction).getActions());
			} else if (actionAction instanceof XcfaLoadAction) {
				memoryModelBuilder.addProgramLoc(((XcfaLoadAction) actionAction).getGlobal());
				memoryModelBuilder.addReadProgramLoc(((XcfaLoadAction) actionAction).getUniqeObject(), currentProcess, ((XcfaLoadAction) actionAction).getGlobal());
				memoryModelBuilder.addPoEdge(pos.get(currentProcess), ((XcfaLoadAction) actionAction).getUniqeObject());
				pos.put(currentProcess, ((XcfaLoadAction) actionAction).getUniqeObject());
				reads.add(Tuple2.of(((XcfaLoadAction) actionAction).getUniqeObject(), ((XcfaLoadAction) actionAction).getSsaValue().getConstDecl(0)));
			} else if (actionAction instanceof XcfaStoreAction) {
				memoryModelBuilder.addProgramLoc(((XcfaStoreAction) actionAction).getGlobal());
				memoryModelBuilder.addWriteProgramLoc(((XcfaStoreAction) actionAction).getUniqeObject(), currentProcess, ((XcfaStoreAction) actionAction).getGlobal());
				memoryModelBuilder.addPoEdge(pos.get(currentProcess), ((XcfaStoreAction) actionAction).getUniqeObject());
				pos.put(currentProcess, ((XcfaStoreAction) actionAction).getUniqeObject());
				writes.add(Tuple2.of(((XcfaStoreAction) actionAction).getUniqeObject(), ((XcfaStoreAction) actionAction).getSsaValue().getConstDecl(0)));
			} else if (actionAction instanceof XcfaThreadChangeAction) {
				currentProcess = ((XcfaThreadChangeAction) actionAction).getProcess();
				memoryModelBuilder.addProgramLoc(currentProcess);
			} else if (actionAction instanceof XcfaLabelAction)
				if (((XcfaLabelAction) actionAction).getLabel() instanceof XcfaLabel.FenceXcfaLabel) {
					final Object uniqueObject = new Object();
					memoryModelBuilder.addFenceLoc(uniqueObject, currentProcess);
					memoryModelBuilder.addPoEdge(pos.get(currentProcess), uniqueObject);
					pos.put(currentProcess, uniqueObject);
				} else if (((XcfaLabelAction) actionAction).getLabel() instanceof XcfaLabel.StartThreadXcfaLabel) {
					Integer threadIdx = counter++;
					Object startingPo = new Object();
					memoryModelBuilder.addProgramLoc(startingPo);
					memoryModelBuilder.addPoEdge(pos.get(currentProcess), startingPo);
					pos.put(threadIdx, startingPo);
					lut.put(((XcfaLabel.StartThreadXcfaLabel) ((XcfaLabelAction) actionAction).getLabel()).getKey(), threadIdx);
				} else if (((XcfaLabelAction) actionAction).getLabel() instanceof XcfaLabel.JoinThreadXcfaLabel) {
					Integer threadIdx = lut.get(((XcfaLabel.JoinThreadXcfaLabel) ((XcfaLabelAction) actionAction).getLabel()).getKey());
					Object newPo = new Object();
					memoryModelBuilder.addProgramLoc(threadIdx);
					memoryModelBuilder.addProgramLoc(newPo);
					memoryModelBuilder.addPoEdge(pos.get(currentProcess), newPo);
					pos.put(currentProcess, newPo);
					memoryModelBuilder.addPoEdge(threadIdx, newPo);
				}
		}
	}

	private static class CollectorSolver implements Solver {
		private final List<Expr<BoolType>> list;

		private CollectorSolver() {
			list = new ArrayList<>();
		}

		@Override
		public void add(Expr<BoolType> assertion) {
			list.add(assertion);
		}

		@Override
		public SolverStatus check() {
			throw new UnsupportedOperationException();
		}

		@Override
		public void push() {
			throw new UnsupportedOperationException();

		}

		@Override
		public void pop(int n) {
			throw new UnsupportedOperationException();

		}

		@Override
		public void reset() {
			throw new UnsupportedOperationException();

		}

		@Override
		public SolverStatus getStatus() {
			throw new UnsupportedOperationException();
		}

		@Override
		public Valuation getModel() {
			throw new UnsupportedOperationException();
		}

		@Override
		public Collection<Expr<BoolType>> getAssertions() {
			return list;
		}

		@Override
		public void close() throws Exception {
			throw new UnsupportedOperationException();

		}
	}
}
