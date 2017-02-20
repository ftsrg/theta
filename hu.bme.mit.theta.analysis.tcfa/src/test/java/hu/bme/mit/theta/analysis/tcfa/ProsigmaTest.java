package hu.bme.mit.theta.analysis.tcfa;

import static hu.bme.mit.theta.core.expr.impl.Exprs.True;

import java.util.function.Predicate;

import org.junit.Test;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgBuilder;
import hu.bme.mit.theta.analysis.algorithm.cegar.Abstractor;
import hu.bme.mit.theta.analysis.algorithm.cegar.WaitlistBasedAbstractor;
import hu.bme.mit.theta.analysis.expl.ExplAnalysis;
import hu.bme.mit.theta.analysis.expl.ExplPrecision;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.impl.FixedPrecisionAnalysis;
import hu.bme.mit.theta.analysis.impl.NullPrecision;
import hu.bme.mit.theta.analysis.loc.ConstLocPrecision;
import hu.bme.mit.theta.analysis.loc.LocAnalysis;
import hu.bme.mit.theta.analysis.loc.LocState;
import hu.bme.mit.theta.analysis.prod.Prod2Analysis;
import hu.bme.mit.theta.analysis.prod.Prod2State;
import hu.bme.mit.theta.analysis.prod.ProdPrecision;
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

public class ProsigmaTest {

	@Test
	public void test() {
		final TCFA prosigma = TcfaModels.prosigma(3, 7);

		final Solver solver = Z3SolverFactory.getInstace().createSolver();

		final TcfaLts lts = TcfaLts.create(prosigma);

		final Analysis<LocState<Prod2State<ZoneState, ExplState>, TcfaLoc, TcfaEdge>, TcfaAction, NullPrecision> analysis = FixedPrecisionAnalysis
				.create(LocAnalysis.create(prosigma.getInitLoc(),
						Prod2Analysis.create(TcfaZoneAnalysis.getInstance(), ExplAnalysis.create(solver, True()))),
						ConstLocPrecision.create(ProdPrecision.of(ZonePrecision.create(prosigma.getClockVars()),
								ExplPrecision.create(prosigma.getDataVars()))));

		final Predicate<State> target = s -> false;

		final ArgBuilder<LocState<Prod2State<ZoneState, ExplState>, TcfaLoc, TcfaEdge>, TcfaAction, NullPrecision> argBuilder = ArgBuilder
				.create(lts, analysis, target);

		final Abstractor<LocState<Prod2State<ZoneState, ExplState>, TcfaLoc, TcfaEdge>, TcfaAction, NullPrecision> abstractor = WaitlistBasedAbstractor
				.create(argBuilder, LocState::getLoc, FifoWaitlist.supplier());

		final ARG<LocState<Prod2State<ZoneState, ExplState>, TcfaLoc, TcfaEdge>, TcfaAction> arg = abstractor
				.createArg();
		abstractor.check(arg, NullPrecision.getInstance());

		System.out.println(new GraphvizWriter().writeString(ArgVisualizer.visualize(arg)));
	}

}
