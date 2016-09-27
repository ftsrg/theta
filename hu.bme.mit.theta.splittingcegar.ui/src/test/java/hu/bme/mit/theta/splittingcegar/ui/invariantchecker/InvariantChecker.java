package hu.bme.mit.theta.splittingcegar.ui.invariantchecker;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.impl.Exprs;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.formalism.sts.STS;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverManager;
import hu.bme.mit.theta.solver.SolverStatus;

public class InvariantChecker {
	public static boolean check(final STS sts, final Expr<? extends BoolType> invariant, final SolverManager manager) {

		final Solver solver = manager.createSolver(true, true);

		solver.push();

		solver.add(sts.unfoldInv(0));

		// init => invariant
		solver.push();
		solver.add(sts.unfoldInit(0));
		solver.add(sts.unfold(Exprs.Not(invariant), 0));
		solver.check();
		if (solver.getStatus() != SolverStatus.UNSAT) {
			solver.pop();
			return false;
		}
		solver.pop();

		solver.add(sts.unfold(invariant, 0));

		// invariant => spec
		solver.push();
		solver.add(sts.unfold(Exprs.Not(sts.getProp()), 0));
		solver.check();
		if (solver.getStatus() != SolverStatus.UNSAT) {
			solver.pop();
			return false;
		}
		solver.pop();

		solver.add(sts.unfoldInv(1));

		// invariant & trans => invariant'
		solver.add(sts.unfoldTrans(0));
		solver.add(sts.unfold(Exprs.Not(invariant), 1));
		solver.check();
		if (solver.getStatus() != SolverStatus.UNSAT) {
			solver.pop();
			return false;
		}

		return true;
	}
}
