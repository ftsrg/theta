package hu.bme.mit.theta.solver;

import java.util.Collection;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.model.Model;
import hu.bme.mit.theta.core.type.BoolType;

public interface Solver {

	public void add(Expr<? extends BoolType> assertion);

	public default void add(final Iterable<? extends Expr<? extends BoolType>> assertions) {
		for (final Expr<? extends BoolType> assertion : assertions) {
			add(assertion);
		}
	}

	public void track(Expr<? extends BoolType> assertion);

	public default void track(final Iterable<? extends Expr<? extends BoolType>> assertions) {
		for (final Expr<? extends BoolType> assertion : assertions) {
			track(assertion);
		}
	}

	public SolverStatus check();

	public void push();

	public void pop(final int n);

	public default void pop() {
		pop(1);
	}

	public void reset();

	public SolverStatus getStatus();

	public Model getModel();

	public Collection<Expr<? extends BoolType>> getUnsatCore();

	public Collection<Expr<? extends BoolType>> getAssertions();
}
