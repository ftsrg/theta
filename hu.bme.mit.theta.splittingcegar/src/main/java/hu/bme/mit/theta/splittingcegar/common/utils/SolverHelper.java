package hu.bme.mit.theta.splittingcegar.common.utils;

import java.util.Collection;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.utils.impl.PathUtils;
import hu.bme.mit.theta.formalism.sts.STS;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverStatus;

public class SolverHelper {

	public static void unrollAndAssert(final Solver solver, final Collection<Expr<? extends BoolType>> expressions,
			final STS sts, final int k) {
		for (final Expr<? extends BoolType> ex : expressions)
			solver.add(PathUtils.unfold(ex, k));
	}

	public static boolean checkSat(final Solver solver) {
		solver.check();
		if (solver.getStatus() != SolverStatus.SAT && solver.getStatus() != SolverStatus.UNSAT)
			throw new RuntimeException("Solver status " + solver.getStatus());

		return solver.getStatus() == SolverStatus.SAT;
	}
}
