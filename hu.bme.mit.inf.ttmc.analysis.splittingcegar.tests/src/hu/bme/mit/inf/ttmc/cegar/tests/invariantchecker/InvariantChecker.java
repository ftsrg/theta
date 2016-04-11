package hu.bme.mit.inf.ttmc.cegar.tests.invariantchecker;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.solver.Solver;
import hu.bme.mit.inf.ttmc.constraint.solver.SolverStatus;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;
import hu.bme.mit.inf.ttmc.formalism.sts.STSManager;

public class InvariantChecker {
	public static boolean check(final STS sts, final Expr<? extends BoolType> invariant) {
		final STSManager manager = sts.getManager();
		final Solver solver = manager.getSolverFactory().createSolver(true, true);

		solver.push();

		solver.add(sts.unrollInv(0));

		// init => invariant
		solver.push();
		solver.add(sts.unrollInit(0));
		solver.add(sts.unroll(manager.getExprFactory().Not(invariant), 0));
		solver.check();
		if (solver.getStatus() != SolverStatus.UNSAT) {
			solver.pop();
			return false;
		}
		solver.pop();

		solver.add(sts.unroll(invariant, 0));

		// invariant => spec
		solver.push();
		solver.add(sts.unroll(manager.getExprFactory().Not(sts.getProp()), 0));
		solver.check();
		if (solver.getStatus() != SolverStatus.UNSAT) {
			solver.pop();
			return false;
		}
		solver.pop();

		solver.add(sts.unrollInv(1));

		// invariant & trans => invariant'
		solver.add(sts.unrollTrans(0));
		solver.add(sts.unroll(manager.getExprFactory().Not(invariant), 1));
		solver.check();
		if (solver.getStatus() != SolverStatus.UNSAT) {
			solver.pop();
			return false;
		}

		return true;
	}
}
