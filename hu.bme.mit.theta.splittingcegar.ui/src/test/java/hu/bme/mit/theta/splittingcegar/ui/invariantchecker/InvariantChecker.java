package hu.bme.mit.theta.splittingcegar.ui.invariantchecker;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.impl.PathUtils;
import hu.bme.mit.theta.formalism.sts.STS;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.SolverStatus;

public class InvariantChecker {
	public static boolean check(final STS sts, final Expr<BoolType> invariant, final SolverFactory factory) {

		final Solver solver = factory.createSolver();

		// init => invariant
		solver.push();
		solver.add(PathUtils.unfold(sts.getInit(), 0));
		solver.add(PathUtils.unfold(Not(invariant), 0));
		solver.check();
		if (solver.getStatus() != SolverStatus.UNSAT) {
			solver.pop();
			return false;
		}
		solver.pop();

		solver.add(PathUtils.unfold(invariant, 0));

		// invariant => spec
		solver.push();
		solver.add(PathUtils.unfold(Not(sts.getProp()), 0));
		solver.check();
		if (solver.getStatus() != SolverStatus.UNSAT) {
			solver.pop();
			return false;
		}
		solver.pop();

		solver.push();
		// invariant & trans => invariant'
		solver.add(PathUtils.unfold(sts.getTrans(), 0));
		solver.add(PathUtils.unfold(Not(invariant), 1));
		solver.check();
		if (solver.getStatus() != SolverStatus.UNSAT) {
			solver.pop();
			return false;
		}
		solver.pop();

		return true;
	}
}
