package hu.bme.mit.theta.xcfa.analysis.declarative.oota;

import com.google.common.collect.Sets;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceStatus;
import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation;
import hu.bme.mit.theta.analysis.expr.refinement.Refutation;
import hu.bme.mit.theta.cat.models.CoherenceMemory;
import hu.bme.mit.theta.cat.solver.BoolDatalogMemoryModelBuilder;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.TupleN;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.booltype.AndExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverStatus;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;
import hu.bme.mit.theta.xcfa.model.XcfaProcess;
import hu.bme.mit.theta.xcfa.model.utils.ExpressionReplacer;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.decl.Decls.Const;
import static hu.bme.mit.theta.core.stmt.Stmts.Assign;
import static hu.bme.mit.theta.core.stmt.Stmts.Assume;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;
import static hu.bme.mit.theta.xcfa.model.XcfaLabel.Stmt;
import static hu.bme.mit.theta.xcfa.model.utils.XcfaLabelVarReplacer.replaceVars;

public class XcfaDeclarativeChecker<R extends Refutation> implements ExprTraceChecker<R> {
	private final ExprTraceChecker<R> traceChecker;
	private final boolean preCheck;

	private XcfaDeclarativeChecker(final ExprTraceChecker<R> traceChecker, final boolean preCheck) {
		this.traceChecker = traceChecker;
		this.preCheck = preCheck;
	}

	// TODO: remove solver
	public static <R extends Refutation> XcfaDeclarativeChecker<R> create(final ExprTraceChecker<R> traceChecker, final Solver solver, final boolean preCheck) {
		return new XcfaDeclarativeChecker<R>(traceChecker, preCheck);
	}

	@Override
	public ExprTraceStatus<R> check(Trace<? extends ExprState, ? extends ExprAction> trace) {
		ExprTraceStatus<R> result = null;
		if(preCheck) {
			result = traceChecker.check(trace);
			if(result.isInfeasible() || !ArchitectureConfig.multiThreading) return result;
		}

		final boolean containsLoads = trace.getActions().stream().filter(exprAction -> exprAction instanceof XcfaDeclarativeAction).anyMatch(exprAction -> ((XcfaDeclarativeAction) exprAction).getLabels().stream().anyMatch(label -> label instanceof XcfaLabel.LoadXcfaLabel));
		if(!containsLoads) {
			if(preCheck) return result;
			else return traceChecker.check(trace);
		}

		final Solver solver = new CollectorSolver();
		BoolDatalogMemoryModelBuilder programBuilder = BoolDatalogMemoryModelBuilder.create(new CoherenceMemory(), solver);

		final List<Tuple2<?, ConstDecl<?>>> dataFlowW = new ArrayList<>();
		final List<Tuple2<?, ConstDecl<?>>> dataFlowR = new ArrayList<>();
		final Map<ConstDecl<?>, Set<Tuple2<XcfaProcess, Decl<?>>>> dataflowLut = new LinkedHashMap<>();
		final List<XcfaDeclarativeAction> newActions = new ArrayList<>();
		checkState(trace.getState(0) instanceof XcfaDeclarativeState, "Wrong type for XcfaDeclarativeState");
		Object lastPo = getSingleton(Tuple2.of(((XcfaDeclarativeState<?>) trace.getState(0)).getCurrentLoc().getParent().getParent(), ProcessLabel.START));
		programBuilder.addProgramLoc(lastPo);
		final Map<VarDecl<?>, XcfaProcess> varLut = new LinkedHashMap<>();

		for (ExprAction action : trace.getActions()) {
			checkState(action instanceof XcfaDeclarativeAction, "Wrong type for XcfaDeclarativeChecker!");
			XcfaDeclarativeAction xcfaAction = (XcfaDeclarativeAction) action;
			if(xcfaAction instanceof XcfaDeclarativeAction.XcfaDeclarativeThreadChangeAction) {
				newActions.add(xcfaAction);
				programBuilder.addProgramLoc(getSingleton(Tuple2.of(xcfaAction.getSource().getParent().getParent(), ProcessLabel.END)));
				programBuilder.addPoEdge(lastPo, getSingleton(Tuple2.of(xcfaAction.getSource().getParent().getParent(), ProcessLabel.END)));
				lastPo = getSingleton(Tuple2.of(xcfaAction.getTarget().getParent().getParent(), ProcessLabel.START));
				programBuilder.addProgramLoc(lastPo);
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
						final ConstDecl<?> var = Const("dataflow" + dataFlowW.size() + dataFlowR.size(), ((XcfaLabel.StoreXcfaLabel<?>) label).getLocal().getType());
						dataFlowW.add(Tuple2.of((XcfaLabel.StoreXcfaLabel<?>) label, var));
						dataflowLut.putIfAbsent(var, new LinkedHashSet<>());
						dataflowLut.get(var).add(Tuple2.of(process, ((XcfaLabel.StoreXcfaLabel<?>) label).getGlobal()));
						newLabels.add(Stmt(Assume(Eq(cast(var.getRef(), var.getType()), cast(((XcfaLabel.StoreXcfaLabel<?>) label).getLocal().getRef(), var.getType())))));
					} else if (label instanceof XcfaLabel.LoadXcfaLabel<?>) {
						programBuilder.addProgramLoc(((XcfaLabel.LoadXcfaLabel<?>) label).getGlobal());
						programBuilder.addReadProgramLoc(label, process, ((XcfaLabel.LoadXcfaLabel<?>) label).getGlobal());
						programBuilder.addPoEdge(lastPo, label);
						lastPo = label;
						final ConstDecl<?> var = Const("dataflow" + dataFlowW.size() + dataFlowR.size(), ((XcfaLabel.LoadXcfaLabel<?>) label).getLocal().getType());
						dataFlowR.add(Tuple2.of((XcfaLabel.LoadXcfaLabel<?>) label, var));
						dataflowLut.putIfAbsent(var, new LinkedHashSet<>());
						dataflowLut.get(var).add(Tuple2.of(process, ((XcfaLabel.LoadXcfaLabel<?>) label).getGlobal()));
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
				newActions.add(XcfaDeclarativeAction.create(XcfaEdge.of(xcfaAction.getSource(), xcfaAction.getTarget(), newLabels)));
			}
		}
		programBuilder.addConstraints(dataFlowW, dataFlowR);
		final AndExpr memoryModel = And(solver.getAssertions());

		final ExprTraceStatus<R> check = traceChecker.check(Trace.of(trace.getStates().stream().map(exprState -> {
			checkState(exprState instanceof XcfaDeclarativeState, "Wrong type of state!");
			return ((XcfaDeclarativeState<?>) exprState).addInvariant(memoryModel);
		}).collect(Collectors.toList()), newActions));
		if(check.isFeasible()) {
			final Valuation model = check.asFeasible().getValuations().getState(check.asFeasible().getValuations().length());
			final List<TupleN<?>> rf = programBuilder.get("rf", model);
			final List<TupleN<Integer>> rfNum = programBuilder.getNumbered("rf", model);
			final List<TupleN<Integer>> coNum = programBuilder.getNumbered("co", model);
			final List<TupleN<?>> co = programBuilder.get("co", model);
			final List<TupleN<?>> po = programBuilder.get("po", model);
			final List<TupleN<?>> loc = programBuilder.get("loc", model);
			final List<TupleN<?>> poRaw = programBuilder.get("poRaw", model);
			final List<TupleN<?>> r = programBuilder.get("R", model);
			final List<TupleN<?>> w = programBuilder.get("W", model);

			System.err.println("Dataflow:");
			for (Tuple2<?, ConstDecl<?>> tup : dataFlowR) {
				System.err.println(tup.get2().getName() + " ( " + programBuilder.getIndexOf(tup.get1()) + " ) := " + ((IntLitExpr)model.eval(tup.get2()).get()).getValue().longValue());
			}
			for (Tuple2<?, ConstDecl<?>> tup : dataFlowW) {
				System.err.println(tup.get2().getName() + " ( " + programBuilder.getIndexOf(tup.get1()) + " ) := " + ((IntLitExpr)model.eval(tup.get2()).get()).getValue().longValue());
			}

			System.err.println("R: ");
			for (TupleN<?> objects : r) {
				System.err.println(objects.get(0));
			}
			System.err.println("==============");

			System.err.println("W: ");
			for (TupleN<?> objects : w) {
				System.err.println(objects.get(0));
			}
			System.err.println("==============");

			System.err.println("rf: ");
			for (TupleN<?> objects : rf) {
				System.err.println(objects.get(0) + "(" + model.eval(((XcfaLabel.StoreXcfaLabel<?>)objects.get(0)).getLocal()) +  ") -> " + objects.get(1));
			}
			System.err.println("==============");

			System.err.println("co: ");
			for (TupleN<?> objects : co) {
				System.err.println(objects.get(0) + " -> " + objects.get(1));
			}
			System.err.println("==============");

			System.err.println("po: ");
			for (TupleN<?> objects : po) {
				System.err.println(objects.get(0) + " -> " + objects.get(1));
			}
			System.err.println("==============");

			System.err.println("loc: ");
			for (TupleN<?> objects : loc) {
				System.err.println(objects.get(0) + " -> " + objects.get(1));
			}
			System.err.println("==============");

			System.err.println("rfNum: ");
			for (TupleN<?> objects : rfNum) {
				System.err.println(objects.get(0) + " -> " + objects.get(1) + " [constraint=false,color=red]");
			}
			System.err.println("==============");

			System.err.println("coNum: ");
			for (TupleN<?> objects : rfNum) {
				System.err.println(objects.get(0) + " -> " + objects.get(1) + " [constraint=false,color=orange]");
			}
			System.err.println("==============");

			System.err.println("poRaw: ");
			for (TupleN<?> objects : poRaw) {
				System.err.println(objects.get(0) + " -> " + objects.get(1));
			}

			List<?> primitives = programBuilder.getPrimitives();
			for (int i = 0; i < primitives.size(); i++) {
				Object primitive = primitives.get(i);
				System.err.println(i + "[label=\"" + primitive + "\"]");
			}
		} else {
			final ExprTraceStatus.Infeasible<R> ref = check.asInfeasible();
			R refutation = ref.asInfeasible().getRefutation();
			if(refutation instanceof ItpRefutation) {
				final List<Expr<BoolType>> exprs = new ArrayList<>();
				for (Expr<BoolType> boolTypeExpr : ((ItpRefutation) refutation).toList()) {
					final Set<Decl<?>> vars = new LinkedHashSet<>();
					ExpressionReplacer.replace(boolTypeExpr, expr -> {
						if(expr instanceof RefExpr) {
							vars.add(((RefExpr<?>) expr).getDecl());
						}
						return Optional.empty();
					});
					final List<Map.Entry<ConstDecl<?>, Set<Tuple2<XcfaProcess, Decl<?>>>>> entries = dataflowLut.entrySet().stream().filter(e -> vars.contains(e.getKey())).collect(Collectors.toList());
					final Set<List<Tuple2<XcfaProcess, Decl<?>>>> lists = Sets.cartesianProduct(entries.stream().map(Map.Entry::getValue).collect(Collectors.toList()));
					for (List<Tuple2<XcfaProcess, Decl<?>>> list : lists) {
						Map<ConstDecl<?>, Decl<?>> lut = new LinkedHashMap<>();
						for (int i = 0; i < list.size(); i++) {
							Decl<?> decl = list.get(i).get2();
							lut.put(entries.get(i).getKey(), decl);
						}
						exprs.add(replaceVars(boolTypeExpr, lut));
					}
				}

				refutation = (R) ItpRefutation.sequence(exprs);
			}  else throw new UnsupportedOperationException("Unsupported refutation: " + refutation);
			return ExprTraceStatus.infeasible(refutation);
		}
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

	private class CollectorSolver implements Solver {
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
