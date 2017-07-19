package hu.bme.mit.theta.solver.utils;

import java.io.Closeable;

import hu.bme.mit.theta.solver.Solver;

/**
 * A helper class for automatic push and pop for solvers using the
 * try-with-resources statement.
 */
public class WithPushPop implements Closeable {

	private final Solver solver;

	public WithPushPop(final Solver solver) {
		this.solver = solver;
		solver.push();
	}

	@Override
	public void close() {
		solver.pop();
	}

}
