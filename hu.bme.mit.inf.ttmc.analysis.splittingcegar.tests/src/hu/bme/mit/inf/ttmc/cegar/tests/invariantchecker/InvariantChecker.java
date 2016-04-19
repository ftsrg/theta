package hu.bme.mit.inf.ttmc.cegar.tests.invariantchecker;

import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.expr.impl.Exprs;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;
import hu.bme.mit.inf.ttmc.solver.Solver;
import hu.bme.mit.inf.ttmc.solver.SolverManager;
import hu.bme.mit.inf.ttmc.solver.SolverStatus;

public class InvariantChecker {
	public static boolean check(final STS sts, final Expr<? extends BoolType> invariant, final SolverManager manager) {

		final Solver solver = manager.getSolverFactory().createSolver(true, true);

		solver.push();

		solver.add(sts.unrollInv(0));

		// init => invariant
		solver.push();
		solver.add(sts.unrollInit(0));
		solver.add(sts.unroll(Exprs.Not(invariant), 0));
		solver.check();
		if (solver.getStatus() != SolverStatus.UNSAT) {
			solver.pop();
			return false;
		}
		solver.pop();

		solver.add(sts.unroll(invariant, 0));

		// invariant => spec
		solver.push();
		solver.add(sts.unroll(Exprs.Not(sts.getProp()), 0));
		solver.check();
		if (solver.getStatus() != SolverStatus.UNSAT) {
			solver.pop();
			return false;
		}
		solver.pop();

		solver.add(sts.unrollInv(1));

		// invariant & trans => invariant'
		solver.add(sts.unrollTrans(0));
		solver.add(sts.unroll(Exprs.Not(invariant), 1));
		solver.check();
		if (solver.getStatus() != SolverStatus.UNSAT) {
			solver.pop();
			return false;
		}

		return true;
	}
}
