package hu.bme.mit.theta.solver;

import java.util.Collection;

import hu.bme.mit.theta.core.model.Model;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

class SolverStub implements Solver {

	int nPush;

	public SolverStub() {
		nPush = 0;
	}

	@Override
	public void add(final Expr<BoolType> assertion) {
	}

	@Override
	public void track(final Expr<BoolType> assertion) {
	}

	@Override
	public SolverStatus check() {
		return null;
	}

	@Override
	public void push() {
		++nPush;
	}

	@Override
	public void pop(final int n) {
		nPush -= n;
	}

	@Override
	public void reset() {
	}

	@Override
	public SolverStatus getStatus() {
		return null;
	}

	@Override
	public Model getModel() {
		return null;
	}

	@Override
	public Collection<Expr<BoolType>> getUnsatCore() {
		return null;
	}

	@Override
	public Collection<Expr<BoolType>> getAssertions() {
		return null;
	}

}
