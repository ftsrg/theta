package hu.bme.mit.inf.ttmc.constraint.z3.solver;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map;

import com.microsoft.z3.Context;
import com.microsoft.z3.Status;

import hu.bme.mit.inf.ttmc.common.Stack;
import hu.bme.mit.inf.ttmc.common.impl.StackImpl;
import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.solver.Model;
import hu.bme.mit.inf.ttmc.constraint.solver.Solver;
import hu.bme.mit.inf.ttmc.constraint.solver.SolverStatus;
import hu.bme.mit.inf.ttmc.constraint.solver.impl.WrapperExpr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;

import static com.google.common.base.Preconditions.checkState;
import static com.google.common.base.Preconditions.checkNotNull;

public class Z3Solver implements Solver {

	private final ConstraintManager manager;
	private final Context context;
	private final Z3TermWrapper termWrapper;

	private final com.microsoft.z3.Solver z3Solver;

	private final Stack<Expr<? extends BoolType>> assertions;
	private final Map<String, Expr<? extends BoolType>> assumptions;

	private Model model;
	private Collection<Expr<? extends BoolType>> unsatCore;
	private SolverStatus status;

	private static final String ASSUMPTION_LABEL = "_LABEL_%d";
	private int labelNum = 0;

	public Z3Solver(final ConstraintManager manager, final Context context, final Z3TermWrapper termWrapper) {
		this(manager, context, context.mkSimpleSolver(), termWrapper);
	}

	public Z3Solver(final ConstraintManager manager, final Context context, final com.microsoft.z3.Solver z3Solver,
			final Z3TermWrapper termWrapper) {
		this.manager = manager;
		this.context = context;
		this.termWrapper = termWrapper;
		this.z3Solver = z3Solver;

		assertions = new StackImpl<>();
		assumptions = new HashMap<>();

		setStatus(SolverStatus.UNKNOWN);
	}

	////

	private void setStatus(SolverStatus status) {
		this.status = status;
		model = null;
		unsatCore = null;
	}

	private Model extractModel() {
		checkState(status == SolverStatus.SAT);
		checkState(model == null);

		final com.microsoft.z3.Model z3Model = z3Solver.getModel();
		checkNotNull(z3Model);

		return new Z3Model(manager, termWrapper, z3Model);
	}

	private Collection<Expr<? extends BoolType>> extractUnsatCore() {
		checkState(status == SolverStatus.UNSAT);
		checkState(unsatCore == null);

		final Collection<Expr<? extends BoolType>> unsatCore = new LinkedList<>();

		final com.microsoft.z3.Expr[] z3UnsatCore = z3Solver.getUnsatCore();

		for (int i = 0; i < z3UnsatCore.length; i = i + 1) {
			final com.microsoft.z3.Expr term = z3UnsatCore[i];

			checkState(term.isConst());

			final String label = term.toString();
			final Expr<? extends BoolType> assumption = assumptions.get(label);

			checkNotNull(assumption);
			unsatCore.add(assumption);
		}

		return unsatCore;
	}

	private com.microsoft.z3.Expr extractTerm(final Expr<?> expr) {
		final WrapperExpr<?, ?> wExpr = (WrapperExpr<?, ?>) expr;

		final com.microsoft.z3.Expr term = (com.microsoft.z3.Expr) wExpr.getTerm();
		checkNotNull(term);

		return term;
	}

	////

	@Override
	public void add(Expr<? extends BoolType> assertion) {
		checkNotNull(assertion);

		assertions.add(assertion);
		final com.microsoft.z3.BoolExpr term = (com.microsoft.z3.BoolExpr) extractTerm(assertion);
		z3Solver.add(term);

		setStatus(SolverStatus.UNKNOWN);
	}

	@Override
	public void track(Expr<? extends BoolType> assertion) {
		checkNotNull(assertion);

		labelNum = labelNum + 1;

		assertions.add(assertion);
		final com.microsoft.z3.BoolExpr term = (com.microsoft.z3.BoolExpr) extractTerm(assertion);
		final String label = String.format(ASSUMPTION_LABEL, labelNum);
		final com.microsoft.z3.BoolExpr labelTerm = context.mkBoolConst(label);

		assumptions.put(label, assertion);

		z3Solver.assertAndTrack(term, labelTerm);

		setStatus(SolverStatus.UNKNOWN);
	}

	@Override
	public SolverStatus check() {
		final Status z3Status = z3Solver.check();

		if (z3Status == Status.SATISFIABLE) {
			setStatus(SolverStatus.SAT);
		} else if (z3Status == Status.UNSATISFIABLE) {
			setStatus(SolverStatus.UNSAT);
		} else {
			setStatus(SolverStatus.UNKNOWN);
		}

		return status;
	}

	@Override
	public void push() {
		assertions.push();
		z3Solver.push();
	}

	@Override
	public void pop(final int n) {
		assertions.pop(n);
		z3Solver.pop(n);

		setStatus(SolverStatus.UNKNOWN);
	}

	@Override
	public void reset() {
		throw new UnsupportedOperationException();
	}

	@Override
	public SolverStatus getStatus() {
		return status;
	}

	@Override
	public Model getModel() {
		checkState(status == SolverStatus.SAT);

		if (model == null) {
			model = extractModel();
		}

		checkNotNull(model);
		return model;
	}

	@Override
	public Collection<Expr<? extends BoolType>> getUnsatCore() {
		checkState(status == SolverStatus.UNSAT);

		if (unsatCore == null) {
			unsatCore = extractUnsatCore();
		}

		checkNotNull(unsatCore);
		return Collections.unmodifiableCollection(unsatCore);
	}

	@Override
	public Collection<Expr<? extends BoolType>> getAssertions() {
		return assertions.toCollection();
	}

}
