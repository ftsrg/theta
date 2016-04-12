package hu.bme.mit.inf.ttmc.cegar.tests.invariantchecker;

import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;
import hu.bme.mit.inf.ttmc.formalism.sts.STSManager;
import hu.bme.mit.inf.ttmc.formalism.sts.STSUnroller;
import hu.bme.mit.inf.ttmc.solver.Solver;
import hu.bme.mit.inf.ttmc.solver.SolverStatus;

public class InvariantChecker {
	public static boolean check(final STS system, final STSUnroller unroller,
			final Expr<? extends BoolType> invariant) {
		final STSManager manager = system.getManager();
		final Solver solver = manager.getSolverFactory().createSolver(true, true);

		solver.push();

		solver.add(unroller.inv(0));

		// init => invariant
		solver.push();
		solver.add(unroller.init(0));
		solver.add(unroller.unroll(manager.getExprFactory().Not(invariant), 0));
		solver.check();
		if (solver.getStatus() != SolverStatus.UNSAT) {
			solver.pop();
			return false;
		}
		solver.pop();

		solver.add(unroller.unroll(invariant, 0));

		// invariant => spec
		solver.push();
		solver.add(unroller.unroll(manager.getExprFactory().Not(system.getProp()), 0));
		solver.check();
		if (solver.getStatus() != SolverStatus.UNSAT) {
			solver.pop();
			return false;
		}
		solver.pop();

		solver.add(unroller.inv(1));

		// invariant & trans => invariant'
		solver.add(unroller.trans(0));
		solver.add(unroller.unroll(manager.getExprFactory().Not(invariant), 1));
		solver.check();
		if (solver.getStatus() != SolverStatus.UNSAT) {
			solver.pop();
			return false;
		}

		return true;
	}
}
