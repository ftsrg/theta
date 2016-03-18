package hu.bme.mit.inf.ttmc.cegar.common.utils;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.solver.Solver;
import hu.bme.mit.inf.ttmc.constraint.solver.SolverStatus;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.sts.STSUnroller;

/**
 * Helper class for TTMCSolvers
 *
 * @author Akos
 */
public class SolverHelper {

	/**
	 * Unroll expressions and assert in solver
	 *
	 * @param solver
	 *            Solver
	 * @param expressions
	 *            List of expressions
	 * @param unroller
	 *            Unroller
	 * @param k
	 *            Unroll to
	 */
	public static void unrollAndAssert(final Solver solver, final Collection<Expr<? extends BoolType>> expressions, final STSUnroller unroller, final int k) {
		for (final Expr<? extends BoolType> ex : expressions)
			solver.add(unroller.unroll(ex, k));
	}

	/**
	 * Check the solver and return if it is satisfiable or not, otherwise throw
	 * an exception
	 *
	 * @param solver
	 *            Solver
	 * @return True if satisfiable, false if unsatisfiable, exception otherwise
	 */
	public static boolean checkSatisfiable(final Solver solver) {
		solver.check();
		if (solver.getStatus() != SolverStatus.SAT && solver.getStatus() != SolverStatus.UNSAT)
			throw new RuntimeException("Solver status " + solver.getStatus());

		return solver.getStatus() == SolverStatus.SAT;
	}
}
