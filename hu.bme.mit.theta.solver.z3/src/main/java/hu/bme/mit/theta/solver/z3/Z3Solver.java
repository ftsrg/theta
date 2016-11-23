package hu.bme.mit.theta.solver.z3;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map;
import java.util.Optional;

import com.google.common.collect.ImmutableList;
import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.Status;

import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.LitExpr;
import hu.bme.mit.theta.core.model.Model;
import hu.bme.mit.theta.core.model.impl.AbstractModel;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverStatus;
import hu.bme.mit.theta.solver.Stack;
import hu.bme.mit.theta.solver.UnknownSolverStatusException;
import hu.bme.mit.theta.solver.impl.StackImpl;
import hu.bme.mit.theta.solver.z3.trasform.Z3SymbolTable;
import hu.bme.mit.theta.solver.z3.trasform.Z3TermTransformer;
import hu.bme.mit.theta.solver.z3.trasform.Z3TransformationManager;

final class Z3Solver implements Solver {

	private final Z3SymbolTable symbolTable;
	private final Z3TransformationManager transformationManager;
	private final Z3TermTransformer termTransformer;

	private final com.microsoft.z3.Context z3Context;
	private final com.microsoft.z3.Solver z3Solver;

	private final Stack<Expr<? extends BoolType>> assertions;
	private final Map<String, Expr<? extends BoolType>> assumptions;

	private static final String ASSUMPTION_LABEL = "_LABEL_%d";
	private int labelNum = 0;

	private Model model;
	private Collection<Expr<? extends BoolType>> unsatCore;
	private SolverStatus status;

	public Z3Solver(final Z3SymbolTable symbolTable, final Z3TransformationManager transformationManager,
			final Z3TermTransformer termTransformer, final com.microsoft.z3.Context z3Context,
			final com.microsoft.z3.Solver z3Solver) {
		this.symbolTable = symbolTable;
		this.transformationManager = transformationManager;
		this.termTransformer = termTransformer;
		this.z3Context = z3Context;
		this.z3Solver = z3Solver;

		assertions = new StackImpl<>();
		assumptions = new HashMap<>();
	}

	////

	@Override
	public void add(final Expr<? extends BoolType> assertion) {
		checkNotNull(assertion);

		assertions.add(assertion);
		final com.microsoft.z3.BoolExpr term = (com.microsoft.z3.BoolExpr) transformationManager.toTerm(assertion);
		z3Solver.add(term);

		clearState();
	}

	@Override
	public void track(final Expr<? extends BoolType> assertion) {
		checkNotNull(assertion);

		assertions.add(assertion);
		final com.microsoft.z3.BoolExpr term = (com.microsoft.z3.BoolExpr) transformationManager.toTerm(assertion);
		final String label = String.format(ASSUMPTION_LABEL, labelNum++);
		final com.microsoft.z3.BoolExpr labelTerm = z3Context.mkBoolConst(label);

		assumptions.put(label, assertion);

		z3Solver.assertAndTrack(term, labelTerm);

		clearState();
	}

	@Override
	public SolverStatus check() {
		final Status z3Status = z3Solver.check();
		status = transformStatus(z3Status);
		return status;
	}

	private SolverStatus transformStatus(final Status z3Status) {
		switch (z3Status) {
		case SATISFIABLE:
			return SolverStatus.SAT;
		case UNSATISFIABLE:
			return SolverStatus.UNSAT;
		default:
			throw new UnknownSolverStatusException();
		}
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
		clearState();
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

		assert model != null;
		return model;
	}

	private Model extractModel() {
		assert status == SolverStatus.SAT;
		assert model == null;

		final com.microsoft.z3.Model z3Model = z3Solver.getModel();
		assert z3Model != null;

		return new Z3Model(z3Model);
	}

	@Override
	public Collection<Expr<? extends BoolType>> getUnsatCore() {
		checkState(status == SolverStatus.UNSAT);

		if (unsatCore == null) {
			unsatCore = extractUnsatCore();
		}

		assert unsatCore != null;
		return Collections.unmodifiableCollection(unsatCore);
	}

	private Collection<Expr<? extends BoolType>> extractUnsatCore() {
		assert status == SolverStatus.UNSAT;
		assert unsatCore == null;

		final Collection<Expr<? extends BoolType>> unsatCore = new LinkedList<>();

		final com.microsoft.z3.Expr[] z3UnsatCore = z3Solver.getUnsatCore();

		for (int i = 0; i < z3UnsatCore.length; i = i + 1) {
			final com.microsoft.z3.Expr term = z3UnsatCore[i];

			checkState(term.isConst());

			final String label = term.toString();
			final Expr<? extends BoolType> assumption = assumptions.get(label);

			assert assumption != null;
			unsatCore.add(assumption);
		}

		return unsatCore;
	}

	@Override
	public Collection<Expr<? extends BoolType>> getAssertions() {
		return assertions.toCollection();
	}

	private void clearState() {
		status = null;
		model = null;
		unsatCore = null;
	}

	////

	private final class Z3Model extends AbstractModel {
		final com.microsoft.z3.Model z3Model;

		final Collection<ConstDecl<?>> constDecls;
		final Map<ConstDecl<?>, LitExpr<?>> constToExpr;

		public Z3Model(final com.microsoft.z3.Model z3Model) {
			this.z3Model = z3Model;
			constDecls = constDeclsOf(z3Model);
			constToExpr = new HashMap<>();
		}

		@Override
		public Collection<? extends ConstDecl<?>> getDecls() {
			return constDecls;
		}

		@Override
		public <DeclType extends Type> Optional<LitExpr<DeclType>> eval(final Decl<DeclType> decl) {
			checkNotNull(decl);
			checkArgument(decl instanceof ConstDecl<?>);

			final ConstDecl<DeclType> constDecl = (ConstDecl<DeclType>) decl;

			LitExpr<?> val = constToExpr.get(constDecl);
			if (val == null) {
				final FuncDecl funcDecl = transformationManager.toSymbol(constDecl);
				final com.microsoft.z3.Expr term = z3Model.getConstInterp(funcDecl);
				if (term != null) {
					val = (LitExpr<?>) termTransformer.toExpr(term);
					constToExpr.put(constDecl, val);
				}
			}

			@SuppressWarnings("unchecked")
			final LitExpr<DeclType> tVal = (LitExpr<DeclType>) val;
			return Optional.of(tVal);
		}

		////

		private Collection<ConstDecl<?>> constDeclsOf(final com.microsoft.z3.Model z3Model) {
			final ImmutableList.Builder<ConstDecl<?>> builder = ImmutableList.builder();
			for (final com.microsoft.z3.FuncDecl symbol : z3Model.getDecls()) {
				if (symbolTable.definesSymbol(symbol)) {
					final ConstDecl<?> constDecl = symbolTable.getConst(symbol);
					builder.add(constDecl);
				} else {
					if (!assumptions.containsKey(symbol.getName().toString())) {
						throw new AssertionError();
					}
				}
			}
			return builder.build();
		}
	}

}
