package hu.bme.mit.inf.ttmc.cegar.common.utils;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.solver.Solver;
import hu.bme.mit.inf.ttmc.constraint.solver.SolverStatus;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;

public class SolverHelper {

	public static void unrollAndAssert(final Solver solver, final Collection<Expr<? extends BoolType>> expressions, final STS sts, final int k) {
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
