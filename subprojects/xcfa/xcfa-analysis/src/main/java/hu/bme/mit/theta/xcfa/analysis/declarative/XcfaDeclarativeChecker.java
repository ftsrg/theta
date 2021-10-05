package hu.bme.mit.theta.xcfa.analysis.declarative;

import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceStatus;
import hu.bme.mit.theta.analysis.expr.refinement.Refutation;
import hu.bme.mit.theta.cat.solver.ProgramBuilder;
import hu.bme.mit.theta.cat.solver.SmtMemoryModelChecker;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;
import hu.bme.mit.theta.xcfa.model.XcfaProcess;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.decl.Decls.Const;
import static hu.bme.mit.theta.core.stmt.Stmts.Assume;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;
import static hu.bme.mit.theta.xcfa.model.XcfaLabel.Stmt;

public class XcfaDeclarativeChecker<R extends Refutation> implements ExprTraceChecker<R> {
	private final ExprTraceChecker<R> traceChecker;
	private final Solver solver;
	private final boolean preCheck;
	private ProgramBuilder<Object, Object, Object> programBuilder;

	private XcfaDeclarativeChecker(final ExprTraceChecker<R> traceChecker, final Solver solver, final boolean preCheck) {
		this.traceChecker = traceChecker;
		this.solver = solver;
		this.preCheck = preCheck;
//		programBuilder = SmtMemoryModelChecker.builder(solver);
	}

	public static <R extends Refutation> XcfaDeclarativeChecker<R> create(final ExprTraceChecker<R> traceChecker, final Solver solver, final boolean preCheck) {
		return new XcfaDeclarativeChecker<R>(traceChecker, solver, preCheck);
	}

	@Override
	public ExprTraceStatus<R> check(Trace<? extends ExprState, ? extends ExprAction> trace) {
		ExprTraceStatus<R> result = null;
		if(preCheck) {
			result = traceChecker.check(trace);
			if(result.isInfeasible()) return result;
		}

		final boolean containsLoads = trace.getActions().stream().filter(exprAction -> exprAction instanceof XcfaDeclarativeAction).anyMatch(exprAction -> ((XcfaDeclarativeAction) exprAction).getLabels().stream().anyMatch(label -> label instanceof XcfaLabel.LoadXcfaLabel));
		if(!containsLoads) return preCheck ? result : traceChecker.check(trace);
		programBuilder = SmtMemoryModelChecker.builder(solver);
//		programBuilder.createUnion("union1", "co", "rf");
//		programBuilder.createUnion("union2", "union1", "fr");
//		programBuilder.createUnion("union3", "union2", "po");
//		programBuilder.assertAcyclic("union3");
		programBuilder.push();
		final List<Tuple2<XcfaLabel, ConstDecl<?>>> dataFlow = new ArrayList<>();
		final List<XcfaDeclarativeAction> newActions = new ArrayList<>();
		checkState(trace.getState(0) instanceof XcfaDeclarativeState, "Wrong type for XcfaDeclarativeState");
		Object lastPo = ((XcfaDeclarativeState<?>) trace.getState(0)).getCurrentLoc().getParent().getParent();
		programBuilder.addProgramLoc(lastPo);
		final Map<VarDecl<?>, XcfaProcess> varLut = new LinkedHashMap<>();

//		XcfaLocation lastLoc = null;
		for (ExprAction action : trace.getActions()) {
			checkState(action instanceof XcfaDeclarativeAction, "Wrong type for XcfaDeclarativeChecker!");
			XcfaDeclarativeAction xcfaAction = (XcfaDeclarativeAction) action;
			if(xcfaAction instanceof XcfaDeclarativeAction.XcfaDeclarativeThreadChangeAction) {
				newActions.add(xcfaAction);
				programBuilder.addProgramLoc(getSingleton(Tuple2.of(xcfaAction.getSource().getParent().getParent(), ProcessLabel.END)));
				programBuilder.addPoEdge(lastPo, getSingleton(Tuple2.of(xcfaAction.getSource().getParent().getParent(), ProcessLabel.END)));
				lastPo = getSingleton(Tuple2.of(xcfaAction.getTarget().getParent().getParent(), ProcessLabel.START));
				programBuilder.addProgramLoc(lastPo);
//				lastLoc = xcfaAction.getTarget();
			} else {
				final List<XcfaLabel> newLabels = new ArrayList<>();
				final XcfaProcess process = xcfaAction.getSource().getParent().getParent();
				programBuilder.addProgramLoc(process);
				for (XcfaLabel label : xcfaAction.getLabels()) {
					if(label instanceof XcfaLabel.StoreXcfaLabel<?>) {
						programBuilder.addProgramLoc(((XcfaLabel.StoreXcfaLabel<?>) label).getGlobal());
						programBuilder.addWriteProgramLoc(label, process, ((XcfaLabel.StoreXcfaLabel<?>) label).getGlobal());
						programBuilder.addPoEdge(lastPo, label);
						lastPo = label;
						final ConstDecl<?> var = Const("dataflow" + dataFlow.size(), ((XcfaLabel.StoreXcfaLabel<?>) label).getLocal().getType());
						dataFlow.add(Tuple2.of(label, var));
						newLabels.add(Stmt(Assume(Eq(cast(var.getRef(), var.getType()), cast(((XcfaLabel.StoreXcfaLabel<?>) label).getLocal().getRef(), var.getType())))));
					} else if (label instanceof XcfaLabel.LoadXcfaLabel<?>) {
						programBuilder.addProgramLoc(((XcfaLabel.LoadXcfaLabel<?>) label).getGlobal());
						programBuilder.addReadProgramLoc(label, process, ((XcfaLabel.LoadXcfaLabel<?>) label).getGlobal());
						programBuilder.addPoEdge(lastPo, label);
						lastPo = label;
						final ConstDecl<?> var = Const("dataflow" + dataFlow.size(), ((XcfaLabel.LoadXcfaLabel<?>) label).getLocal().getType());
						dataFlow.add(Tuple2.of(label, var));
						newLabels.add(Stmt(Assume(Eq(cast(((XcfaLabel.LoadXcfaLabel<?>) label).getLocal().getRef(), var.getType()), cast(var.getRef(), var.getType())))));
					} else if (label instanceof XcfaLabel.FenceXcfaLabel) {
						programBuilder.addFenceLoc(label, process);
						programBuilder.addPoEdge(lastPo, label);
						lastPo = label;
						newLabels.add(label);
					} else if (label instanceof XcfaLabel.StartThreadXcfaLabel) {
						programBuilder.addProgramLoc(label);
						programBuilder.addPoEdge(lastPo, label);
						lastPo = label;
						programBuilder.addProgramLoc(getSingleton(Tuple2.of(((XcfaLabel.StartThreadXcfaLabel) label).getProcess(), ProcessLabel.START)));
						programBuilder.addPoEdge(lastPo, getSingleton(Tuple2.of(((XcfaLabel.StartThreadXcfaLabel) label).getProcess(), ProcessLabel.START)));
						varLut.put(((XcfaLabel.StartThreadXcfaLabel) label).getKey(), ((XcfaLabel.StartThreadXcfaLabel) label).getProcess());
						newLabels.add(label);
					} else if (label instanceof XcfaLabel.JoinThreadXcfaLabel) {
						programBuilder.addProgramLoc(label);
						programBuilder.addPoEdge(lastPo, label);
						lastPo = label;
						final VarDecl<?> key = ((XcfaLabel.JoinThreadXcfaLabel) label).getKey();
						programBuilder.addProgramLoc(getSingleton(Tuple2.of(varLut.get(key), ProcessLabel.END)));
						programBuilder.addPoEdge(getSingleton(Tuple2.of(varLut.get(key), ProcessLabel.END)), label);
						newLabels.add(label);
					} else if (label instanceof XcfaLabel.AtomicBeginXcfaLabel) {
						programBuilder.addProgramLoc(label);
						programBuilder.addPoEdge(lastPo, label);
						lastPo = label;
						newLabels.add(label);
					} else if (label instanceof XcfaLabel.AtomicEndXcfaLabel) {
						programBuilder.addProgramLoc(label);
						programBuilder.addPoEdge(lastPo, label);
						lastPo = label;
						newLabels.add(label);
					} else {
						newLabels.add(label);
					}
				}
//				lastLoc = xcfaAction.getTarget();
				newActions.add(XcfaDeclarativeAction.create(XcfaEdge.of(xcfaAction.getSource(), xcfaAction.getTarget(), newLabels)));
			}
		}
//		final MemoryModelSolver<Object, Object> built = programBuilder.build();
//		final List<Expr<BoolType>> memoryModel = new ArrayList<>();
//		for (Collection<Tuple2<Object, Object>> tuple2s : built.getAllRf()) {
//			final List<Expr<BoolType>> rfSet = new ArrayList<>();
//			for (Tuple2<Object, Object> rf : tuple2s) {
//				rfSet.add(Eq(dataFlow.stream().filter(w -> w.get1() == rf.get1()).findFirst().get().get2().getRef(), dataFlow.stream().filter(r -> r.get1() == rf.get2()).findFirst().get().get2().getRef()));
//			}
//			memoryModel.add(And(rfSet));
//		}
//		final List<ExprState> newStates = new ArrayList<>(trace.getStates());
//		newStates.add(newStates.get(newStates.size() - 1));
//		newActions.add(XcfaDeclarativeAction.create(XcfaEdge.of(lastLoc, lastLoc, List.of(Stmt(Assume(ExprUtils.simplify(Or(memoryModel))))))));
//		final ExprTraceStatus<R> check = traceChecker.check(Trace.of(newStates, newActions));
		programBuilder.build(dataFlow);
		final ExprTraceStatus<R> check = traceChecker.check(Trace.of(trace.getStates(), newActions));
		programBuilder.pop();
		return check;
	}

	private final Map<Object, Object> singletonStore = new LinkedHashMap<>();
	private <T> T getSingleton(T o) {
		singletonStore.putIfAbsent(o, o);
		//noinspection unchecked
		return (T) singletonStore.get(o);
	}

	private enum ProcessLabel {
		START,
		END
	}
}
