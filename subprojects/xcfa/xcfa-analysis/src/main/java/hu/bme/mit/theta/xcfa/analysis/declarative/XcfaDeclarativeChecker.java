package hu.bme.mit.theta.xcfa.analysis.declarative;

import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceStatus;
import hu.bme.mit.theta.analysis.expr.refinement.Refutation;
import hu.bme.mit.theta.cat.solver.MemoryModelChecker;
import hu.bme.mit.theta.cat.solver.MemoryModelSolver;
import hu.bme.mit.theta.cat.solver.ProgramBuilder;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaProcess;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.decl.Decls.Var;
import static hu.bme.mit.theta.core.stmt.Stmts.Assign;
import static hu.bme.mit.theta.core.stmt.Stmts.Assume;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Or;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;
import static hu.bme.mit.theta.xcfa.model.XcfaLabel.Stmt;

public class XcfaDeclarativeChecker<R extends Refutation> implements ExprTraceChecker<R> {
	private final ExprTraceChecker<R> traceChecker;
	private final Solver solver;
	private final boolean preCheck;
	private final ProgramBuilder<Object, Object, Object> programBuilder;

	private XcfaDeclarativeChecker(final ExprTraceChecker<R> traceChecker, final Solver solver, final boolean preCheck) {
		this.traceChecker = traceChecker;
		this.solver = solver;
		this.preCheck = preCheck;
		programBuilder = MemoryModelChecker.builder(solver);
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

		solver.push();
//		String w1 = "w1";
//		String w2 = "w2";
//		String r1 = "r1";
//		String r2 = "r2";
//		model.addUnaryFact("W", w1);
//		model.addUnaryFact("W", w2);
//		model.addUnaryFact("R", r1);
//		model.addUnaryFact("R", r2);
//		model.addBinaryFact("poRaw", w1, w2);
//		model.addBinaryFact("poRaw", r1, r2);
//		model.addBinaryFact("locRaw", w1, w2);
//		model.addBinaryFact("locRaw", r1, r2);
//		model.addBinaryFact("locRaw", r1, w1);
//		model.addBinaryFact("intRaw", r1, r2);
//		model.addBinaryFact("intRaw", w1, w2);
//		model.build().printRf();


		final Map<XcfaLabel, VarDecl<?>> dataFlow = new LinkedHashMap<>();
		final List<XcfaDeclarativeAction> newActions = new ArrayList<>();
		checkState(trace.getState(0) instanceof XcfaDeclarativeState, "Wrong type for XcfaDeclarativeState");
		Object lastPo = ((XcfaDeclarativeState<?>) trace.getState(0)).getCurrentLoc().getParent().getParent();
		programBuilder.addProgramLoc(lastPo);
		final Map<VarDecl<?>, XcfaProcess> varLut = new LinkedHashMap<>();
		XcfaLocation lastLoc = null;
		for (ExprAction action : trace.getActions()) {
			checkState(action instanceof XcfaDeclarativeAction, "Wrong type for XcfaDeclarativeChecker!");
			XcfaDeclarativeAction xcfaAction = (XcfaDeclarativeAction) action;
			if(xcfaAction instanceof XcfaDeclarativeAction.XcfaDeclarativeThreadChangeAction) {
				newActions.add(xcfaAction);
				programBuilder.addProgramLoc(Tuple2.of(xcfaAction.getSource().getParent().getParent(), ProcessLabel.END));
				programBuilder.addPoEdge(lastPo, Tuple2.of(xcfaAction.getSource().getParent().getParent(), ProcessLabel.END));
				lastPo = Tuple2.of(xcfaAction.getTarget().getParent().getParent(), ProcessLabel.START);
				programBuilder.addProgramLoc(lastPo);
				lastLoc = xcfaAction.getTarget();
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
						final VarDecl<?> var = Var("dataflow" + dataFlow.size(), ((XcfaLabel.StoreXcfaLabel<?>) label).getLocal().getType());
						dataFlow.put(label, var);
						newLabels.add(Stmt(Assign(cast(var, var.getType()), cast(((XcfaLabel.StoreXcfaLabel<?>) label).getLocal().getRef(), var.getType()))));
					} else if (label instanceof XcfaLabel.LoadXcfaLabel<?>) {
						programBuilder.addProgramLoc(((XcfaLabel.LoadXcfaLabel<?>) label).getGlobal());
						programBuilder.addReadProgramLoc(label, process, ((XcfaLabel.LoadXcfaLabel<?>) label).getGlobal());
						programBuilder.addPoEdge(lastPo, label);
						lastPo = label;
						final VarDecl<?> var = Var("dataflow" + dataFlow.size(), ((XcfaLabel.LoadXcfaLabel<?>) label).getLocal().getType());
						dataFlow.put(label, var);
						newLabels.add(Stmt(Assign(cast(((XcfaLabel.LoadXcfaLabel<?>) label).getLocal(), var.getType()), cast(var.getRef(), var.getType()))));
					} else if (label instanceof XcfaLabel.FenceXcfaLabel) {
						programBuilder.addFenceLoc(label, process);
						programBuilder.addPoEdge(lastPo, label);
						lastPo = label;
						newLabels.add(label);
					} else if (label instanceof XcfaLabel.StartThreadXcfaLabel) {
						programBuilder.addProgramLoc(label);
						programBuilder.addPoEdge(lastPo, label);
						lastPo = label;
						programBuilder.addProgramLoc(Tuple2.of(((XcfaLabel.StartThreadXcfaLabel) label).getProcess(), ProcessLabel.START));
						programBuilder.addPoEdge(lastPo, Tuple2.of(((XcfaLabel.StartThreadXcfaLabel) label).getProcess(), ProcessLabel.START));
						varLut.put(((XcfaLabel.StartThreadXcfaLabel) label).getKey(), ((XcfaLabel.StartThreadXcfaLabel) label).getProcess());
						newLabels.add(label);
					} else if (label instanceof XcfaLabel.JoinThreadXcfaLabel) {
						programBuilder.addProgramLoc(label);
						programBuilder.addPoEdge(lastPo, label);
						lastPo = label;
						final VarDecl<?> key = ((XcfaLabel.JoinThreadXcfaLabel) label).getKey();
						programBuilder.addProgramLoc(Tuple2.of(varLut.get(key), ProcessLabel.END));
						programBuilder.addPoEdge(Tuple2.of(varLut.get(key), ProcessLabel.END), label);
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
				lastLoc = xcfaAction.getTarget();
				newActions.add(XcfaDeclarativeAction.create(XcfaEdge.of(xcfaAction.getSource(), xcfaAction.getTarget(), newLabels)));
			}
		}
		final MemoryModelSolver<Object, Object> built = programBuilder.build();
		Expr<BoolType> memoryModel = False();
		for (Collection<Tuple2<Object, Object>> tuple2s : built.getAllRf()) {
			Expr<BoolType> rfSet = True();
			for (Tuple2<Object, Object> rf : tuple2s) {
				checkState(dataFlow.containsKey(rf.get1()) && dataFlow.containsKey(rf.get2()), "Loads and stores do not exist!");
				rfSet = And(rfSet, Eq(dataFlow.get(rf.get1()).getRef(), dataFlow.get(rf.get2()).getRef()));
			}
			memoryModel = Or(memoryModel, rfSet);
		}
		final List<ExprState> newStates = new ArrayList<>(trace.getStates());
		newStates.add(newStates.get(newStates.size() - 1));
		newActions.add(XcfaDeclarativeAction.create(XcfaEdge.of(lastLoc, lastLoc, List.of(Stmt(Assume(memoryModel))))));
		solver.pop();
		return traceChecker.check(Trace.of(newStates, newActions));
	}

	private enum ProcessLabel {
		START,
		END
	}
}
