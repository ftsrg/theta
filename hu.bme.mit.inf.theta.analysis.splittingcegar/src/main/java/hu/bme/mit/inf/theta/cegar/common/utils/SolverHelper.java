package hu.bme.mit.inf.theta.cegar.common.utils;

import java.util.Collection;

import hu.bme.mit.inf.theta.core.expr.Expr;
import hu.bme.mit.inf.theta.core.type.BoolType;
import hu.bme.mit.inf.theta.formalism.sts.STS;
import hu.bme.mit.inf.theta.solver.Solver;
import hu.bme.mit.inf.theta.solver.SolverStatus;

public class SolverHelper {

	public static void unrollAndAssert(final Solver solver, final Collection<Expr<? extends BoolType>> expressions,
			final STS sts, final int k) {
		for (final Expr<? extends BoolType> ex : expressions)
			solver.add(sts.unroll(ex, k));
	}

	public static boolean checkSat(final Solver solver) {
		solver.check();
		if (solver.getStatus() != SolverStatus.SAT && solver.getStatus() != SolverStatus.UNSAT)
			throw new RuntimeException("Solver status " + solver.getStatus());

		return solver.getStatus() == SolverStatus.SAT;
	}
}
