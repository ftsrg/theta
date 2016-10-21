package hu.bme.mit.theta.analysis.tcfa.network;

import static hu.bme.mit.theta.core.decl.impl.Decls.Var;
import static hu.bme.mit.theta.core.type.impl.Types.Int;

import org.junit.Test;

import hu.bme.mit.theta.analysis.algorithm.cegar.Abstractor;
import hu.bme.mit.theta.analysis.algorithm.cegar.AbstractorStatus;
import hu.bme.mit.theta.analysis.algorithm.cegar.WaitlistBasedAbstractor;
import hu.bme.mit.theta.analysis.composite.CompositeAnalysis;
import hu.bme.mit.theta.analysis.composite.CompositePrecision;
import hu.bme.mit.theta.analysis.composite.CompositeState;
import hu.bme.mit.theta.analysis.expl.ExplPrecision;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.loc.LocPrecision;
import hu.bme.mit.theta.analysis.loc.LocState;
import hu.bme.mit.theta.analysis.tcfa.TcfaAction;
import hu.bme.mit.theta.analysis.tcfa.TcfaAnalyis;
import hu.bme.mit.theta.analysis.tcfa.expl.TcfaExplAnalysis;
import hu.bme.mit.theta.analysis.tcfa.zone.TcfaZoneAnalysis;
import hu.bme.mit.theta.analysis.utils.ArgVisualizer;
import hu.bme.mit.theta.analysis.zone.ZonePrecision;
import hu.bme.mit.theta.analysis.zone.ZoneState;
import hu.bme.mit.theta.common.visualization.GraphvizWriter;
import hu.bme.mit.theta.common.waitlist.LifoWaitlist;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.IntType;
import hu.bme.mit.theta.formalism.tcfa.TCFA;
import hu.bme.mit.theta.formalism.tcfa.TcfaEdge;
import hu.bme.mit.theta.formalism.tcfa.TcfaLoc;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;

public class TcfaNetworkExplTest {

	@Test
	public void test() {
		final int n = 2;
		final VarDecl<IntType> vlock = Var("lock", Int());
		final TCFA fischer = TcfaNetworkTestHelper.fischer(n, vlock);

		final Solver solver = Z3SolverFactory.getInstace().createSolver();

		final TcfaAnalyis<CompositeState<ZoneState, ExplState>, CompositePrecision<ZonePrecision, ExplPrecision>> analysis = TcfaAnalyis
				.create(fischer.getInitLoc(),
						CompositeAnalysis.create(TcfaZoneAnalysis.getInstance(), TcfaExplAnalysis.create(solver)));

		final CompositePrecision<ZonePrecision, ExplPrecision> subPrecision = CompositePrecision
				.create(ZonePrecision.create(fischer.getClockVars()), ExplPrecision.create(fischer.getDataVars()));
		final LocPrecision<CompositePrecision<ZonePrecision, ExplPrecision>, TcfaLoc, TcfaEdge> precision = LocPrecision
				.create(l -> subPrecision);

		final Abstractor<LocState<CompositeState<ZoneState, ExplState>, TcfaLoc, TcfaEdge>, TcfaAction, LocPrecision<CompositePrecision<ZonePrecision, ExplPrecision>, TcfaLoc, TcfaEdge>> abstractor = WaitlistBasedAbstractor
				.create(analysis, s -> false, new LifoWaitlist<>());

		abstractor.init(precision);
		final AbstractorStatus<LocState<CompositeState<ZoneState, ExplState>, TcfaLoc, TcfaEdge>, TcfaAction> abstractorStatus = abstractor
				.check(precision);

		System.out.println(new GraphvizWriter().writeString(ArgVisualizer.visualize(abstractorStatus.getArg())));
	}

}
