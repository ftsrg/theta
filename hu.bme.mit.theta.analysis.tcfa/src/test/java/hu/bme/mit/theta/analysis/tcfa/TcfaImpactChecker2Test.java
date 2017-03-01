package hu.bme.mit.theta.analysis.tcfa;

import static org.junit.Assert.assertTrue;

import org.junit.Test;

import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.impl.NullPrec;
import hu.bme.mit.theta.analysis.tcfa.impact.TcfaImpactChecker2;
import hu.bme.mit.theta.analysis.utils.ArgVisualizer;
import hu.bme.mit.theta.common.visualization.GraphvizWriter;
import hu.bme.mit.theta.formalism.tcfa.TCFA;
import hu.bme.mit.theta.formalism.tcfa.instances.TcfaModels;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;

public final class TcfaImpactChecker2Test {

	@Test
	public void test() {
		// Arrange
		final int n = 2;
		final TCFA fischer = TcfaModels.fischer(n, 1, 2);

		final Solver solver = Z3SolverFactory.getInstace().createSolver();

		final TcfaImpactChecker2 checker = TcfaImpactChecker2.create(fischer, solver, l -> false);

		// Act
		final SafetyResult<? extends ExprState, ? extends ExprAction> status = checker
				.check(NullPrec.getInstance());

		// Assert
		assertTrue(status.isSafe());
		final ARG<? extends ExprState, ? extends ExprAction> arg = status.getArg();
		arg.minimize();

		final ArgChecker argChecker = ArgChecker.create(solver);
		assertTrue(argChecker.isWellLabeled(arg));

		System.out.println(new GraphvizWriter().writeString(ArgVisualizer.visualize(arg)));
	}

}
