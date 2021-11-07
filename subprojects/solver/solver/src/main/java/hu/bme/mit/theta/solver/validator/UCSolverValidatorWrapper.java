package hu.bme.mit.theta.solver.validator;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.solver.SolverManager;
import hu.bme.mit.theta.solver.SolverStatus;
import hu.bme.mit.theta.solver.UCSolver;

import java.util.Collection;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;

public class UCSolverValidatorWrapper implements UCSolver {
	private final UCSolver solver;
	UCSolverValidatorWrapper(String solver) throws Exception {
		this.solver = SolverManager.resolveSolverFactory(solver).createUCSolver();
	}

	@Override
	public SolverStatus check() {
		SolverStatus check = solver.check();
		if(check.isSat()) {
			final Valuation model = solver.getModel();
			for (Expr<BoolType> assertion : solver.getAssertions()) {
				if(!assertion.eval(model).equals(True())) {
					throw new RuntimeException("Solver problem: " + assertion);
				}
			}
		}
		return check;
	}

	@Override
	public void push() {
		solver.push();
	}

	@Override
	public void pop(int n) {
		solver.pop();
	}

	@Override
	public void reset() {
		solver.reset();
	}

	@Override
	public SolverStatus getStatus() {
		return solver.getStatus();
	}

	@Override
	public Valuation getModel() {
		return solver.getModel();
	}

	@Override
	public Collection<Expr<BoolType>> getAssertions() {
		return solver.getAssertions();
	}

	@Override
	public void close() throws Exception {
		solver.close();
	}

	@Override
	public void track(Expr<BoolType> assertion) {
		solver.track(assertion);
	}

	@Override
	public Collection<Expr<BoolType>> getUnsatCore() {
		return solver.getUnsatCore();
	}
}
