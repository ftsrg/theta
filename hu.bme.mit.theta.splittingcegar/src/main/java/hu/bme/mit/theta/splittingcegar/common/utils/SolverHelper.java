package hu.bme.mit.theta.splittingcegar.common.utils;

import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.formalism.sts.STS;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverStatus;

public class SolverHelper {

	public static void unrollAndAssert(final Solver solver, final Iterable<? extends Expr<BoolType>> expressions,
			final STS sts, final int k) {
		for (final Expr<BoolType> ex : expressions)
			solver.add(PathUtils.unfold(ex, k));
	}

	public static boolean checkSat(final Solver solver) {
		solver.check();
		if (solver.getStatus() != SolverStatus.SAT && solver.getStatus() != SolverStatus.UNSAT)
			throw new RuntimeException("Solver status " + solver.getStatus());

		return solver.getStatus() == SolverStatus.SAT;
	}
}
