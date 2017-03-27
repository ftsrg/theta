package hu.bme.mit.theta.analysis.xta;

import static org.junit.Assert.assertTrue;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.util.Arrays;
import java.util.Collection;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.analysis.utils.ArgVisualizer;
import hu.bme.mit.theta.analysis.xta.algorithm.itp.XtaItpChecker;
import hu.bme.mit.theta.analysis.zone.itp.ItpZoneState;
import hu.bme.mit.theta.common.visualization.GraphvizWriter;
import hu.bme.mit.theta.formalism.xta.XtaSystem;
import hu.bme.mit.theta.formalism.xta.dsl.XtaDslManager;

@RunWith(Parameterized.class)
public final class XtaItpCheckerTest {

	@Parameters(name = "{0}")
	public static Collection<Object[]> data() {
		return Arrays.asList(new Object[][] {

				{ "/critical-2-25-50.xta" },

				{ "/csma-2.xta" },

				{ "/fddi-2.xta" },

				{ "/fischer-2-32-64.xta" },

				{ "/lynch-2-16.xta" }

		});
	}

	@Parameter(0)
	public String filepath;

	@Test
	public void test() throws FileNotFoundException, IOException {
		// Arrange
		final InputStream inputStream = getClass().getResourceAsStream(filepath);
		final XtaSystem system = XtaDslManager.createSystem(inputStream);

		final XtaItpChecker checker = XtaItpChecker.create(system, l -> false);

		// Act
		final SafetyResult<XtaState<ItpZoneState>, XtaAction> status = checker.check(UnitPrec.getInstance());

		// Assert
		assertTrue(status.isSafe());
		final ARG<XtaState<ItpZoneState>, XtaAction> arg = status.getArg();

		// TODO XtaAction implements ExprAction
		// final Solver solver = Z3SolverFactory.getInstace().createSolver();
		// final ArgChecker argChecker = ArgChecker.create(solver);
		// assertTrue(argChecker.isWellLabeled(arg));

		System.out.println(arg.getNodes().count());
		System.out.println(new GraphvizWriter().writeString(ArgVisualizer.visualize(arg)));
	}

}
