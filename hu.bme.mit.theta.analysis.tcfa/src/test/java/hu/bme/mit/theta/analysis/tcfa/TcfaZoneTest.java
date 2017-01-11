package hu.bme.mit.theta.analysis.tcfa;

import static org.junit.Assert.assertTrue;

import java.util.function.Predicate;

import org.junit.Test;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgBuilder;
import hu.bme.mit.theta.analysis.algorithm.ArgChecker;
import hu.bme.mit.theta.analysis.algorithm.cegar.Abstractor;
import hu.bme.mit.theta.analysis.algorithm.cegar.WaitlistBasedAbstractor;
import hu.bme.mit.theta.analysis.impl.FixedPrecisionAnalysis;
import hu.bme.mit.theta.analysis.impl.NullPrecision;
import hu.bme.mit.theta.analysis.loc.LocAnalysis;
import hu.bme.mit.theta.analysis.loc.LocPrecision;
import hu.bme.mit.theta.analysis.loc.LocState;
import hu.bme.mit.theta.analysis.tcfa.zone.TcfaZoneAnalysis;
import hu.bme.mit.theta.analysis.utils.ArgVisualizer;
import hu.bme.mit.theta.analysis.waitlist.FifoWaitlist;
import hu.bme.mit.theta.analysis.zone.ZonePrecision;
import hu.bme.mit.theta.analysis.zone.ZoneState;
import hu.bme.mit.theta.common.visualization.GraphvizWriter;
import hu.bme.mit.theta.formalism.tcfa.TCFA;
import hu.bme.mit.theta.formalism.tcfa.TcfaEdge;
import hu.bme.mit.theta.formalism.tcfa.TcfaLoc;
import hu.bme.mit.theta.formalism.tcfa.instances.TcfaModels;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;

public class TcfaZoneTest {

	@Test
	public void test() {
		final int n = 2;
		final TCFA fischer = TcfaModels.fischer(n, 1, 2);

		final TcfaLts lts = TcfaLts.create(fischer);

		final Analysis<LocState<ZoneState, TcfaLoc, TcfaEdge>, TcfaAction, NullPrecision> analysis = FixedPrecisionAnalysis
				.create(LocAnalysis.create(fischer.getInitLoc(), TcfaZoneAnalysis.getInstance()),
						LocPrecision.constant(ZonePrecision.create(fischer.getClockVars())));

		final Predicate<State> target = s -> false;

		final ArgBuilder<LocState<ZoneState, TcfaLoc, TcfaEdge>, TcfaAction, NullPrecision> argBuilder = ArgBuilder
				.create(lts, analysis, target);

		final Abstractor<LocState<ZoneState, TcfaLoc, TcfaEdge>, TcfaAction, NullPrecision> abstractor = WaitlistBasedAbstractor
				.create(argBuilder, FifoWaitlist.supplier());

		final ARG<LocState<ZoneState, TcfaLoc, TcfaEdge>, TcfaAction> arg = abstractor.createArg();
		abstractor.check(arg, NullPrecision.getInstance());

		System.out.println(new GraphvizWriter().writeString(ArgVisualizer.visualize(arg)));

		final Solver solver = Z3SolverFactory.getInstace().createSolver();

		final ArgChecker checker = ArgChecker.create(solver);
		assertTrue(checker.isWellLabeled(arg));
	}

}
