package hu.bme.mit.theta.solver;

import java.util.Collection;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.model.Model;
import hu.bme.mit.theta.core.type.booltype.BoolType;

public interface Solver {

	void add(Expr<? extends BoolType> assertion);

	default void add(final Iterable<? extends Expr<? extends BoolType>> assertions) {
		for (final Expr<? extends BoolType> assertion : assertions) {
			add(assertion);
		}
	}

	void track(Expr<? extends BoolType> assertion);

	default void track(final Iterable<? extends Expr<? extends BoolType>> assertions) {
		for (final Expr<? extends BoolType> assertion : assertions) {
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

	Collection<Expr<? extends BoolType>> getUnsatCore();

	Collection<Expr<? extends BoolType>> getAssertions();
}
