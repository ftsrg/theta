package hu.bme.mit.theta.analysis.tcfa;

import static org.junit.Assert.assertTrue;

import org.junit.Test;

import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.impl.NullPrec;
import hu.bme.mit.theta.analysis.tcfa.lawi.TcfaLawiChecker;
import hu.bme.mit.theta.analysis.tcfa.lawi.TcfaLawiState;
import hu.bme.mit.theta.formalism.tcfa.TCFA;
import hu.bme.mit.theta.formalism.tcfa.instances.TcfaModels;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;

public final class TcfaLawiCheckerTest {

	@Test
	public void test() {
		// Arrange
		final int n = 2;
		final TCFA fischer = TcfaModels.fischer(n, 2);

		final TcfaLawiChecker checker = TcfaLawiChecker.create(fischer, l -> false);

		// Act
		final SafetyResult<TcfaLawiState, TcfaAction> status = checker.check(NullPrec.getInstance());

		// Assert
		assertTrue(status.isSafe());
		final ARG<TcfaLawiState, TcfaAction> arg = status.getArg();

		final Solver solver = Z3SolverFactory.getInstace().createSolver();
		final ArgChecker argChecker = ArgChecker.create(solver);
		assertTrue(argChecker.isWellLabeled(arg));

		System.out.println(arg.getNodes().count());
	}

}
