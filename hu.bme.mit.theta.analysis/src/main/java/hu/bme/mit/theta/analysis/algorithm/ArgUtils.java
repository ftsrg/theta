package hu.bme.mit.theta.analysis.algorithm;

import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.solver.Solver;

public final class ArgUtils {

	private ArgUtils() {
	}

	public static <S extends ExprState, A extends ExprAction> boolean isWellLabeled(final ARG<S, A> arg,
			final Solver solver) {
		return ArgChecker.create(solver).isWellLabeled(arg);
	}

}
