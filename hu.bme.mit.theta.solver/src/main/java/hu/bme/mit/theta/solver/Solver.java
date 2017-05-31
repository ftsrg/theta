package hu.bme.mit.theta.solver;

import java.util.Collection;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.model.Model;
import hu.bme.mit.theta.core.type.booltype.BoolType;

public interface Solver {

	void add(Expr<BoolType> assertion);

	default void add(final Iterable<? extends Expr<BoolType>> assertions) {
		for (final Expr<BoolType> assertion : assertions) {
			add(assertion);
		}
	}

	void track(Expr<BoolType> assertion);

	default void track(final Iterable<? extends Expr<BoolType>> assertions) {
		for (final Expr<BoolType> assertion : assertions) {
			track(assertion);
		}
	}

	SolverStatus check();

	void push();

	void pop(final int n);

	default void pop() {
		pop(1);
	}

	void reset();

	SolverStatus getStatus();

	Model getModel();

	Collection<Expr<BoolType>> getUnsatCore();

	Collection<Expr<BoolType>> getAssertions();
}
