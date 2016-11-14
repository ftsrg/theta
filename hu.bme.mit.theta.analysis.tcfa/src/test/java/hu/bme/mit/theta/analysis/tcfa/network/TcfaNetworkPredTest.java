package hu.bme.mit.theta.analysis.tcfa.network;

import static hu.bme.mit.theta.core.decl.impl.Decls.Var;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Eq;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Int;
import static hu.bme.mit.theta.core.type.impl.Types.Int;

import java.util.Arrays;

import org.junit.Test;

import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.cegar.Abstractor;
import hu.bme.mit.theta.analysis.algorithm.cegar.WaitlistBasedAbstractor;
import hu.bme.mit.theta.analysis.composite.CompositeAnalysis;
import hu.bme.mit.theta.analysis.composite.CompositePrecision;
import hu.bme.mit.theta.analysis.composite.CompositeState;
import hu.bme.mit.theta.analysis.loc.LocPrecision;
import hu.bme.mit.theta.analysis.loc.LocState;
import hu.bme.mit.theta.analysis.pred.PredPrecision;
import hu.bme.mit.theta.analysis.pred.PredState;
import hu.bme.mit.theta.analysis.pred.SimplePredPrecision;
import hu.bme.mit.theta.analysis.tcfa.TcfaAction;
import hu.bme.mit.theta.analysis.tcfa.TcfaAnalyis;
import hu.bme.mit.theta.analysis.tcfa.pred.TcfaPredAnalysis;
import hu.bme.mit.theta.analysis.tcfa.zone.TcfaZoneAnalysis;
import hu.bme.mit.theta.analysis.utils.ArgVisualizer;
import hu.bme.mit.theta.analysis.zone.ZonePrecision;
import hu.bme.mit.theta.analysis.zone.ZoneState;
import hu.bme.mit.theta.common.visualization.GraphvizWriter;
import hu.bme.mit.theta.common.waitlist.FifoWaitlist;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.IntType;
import hu.bme.mit.theta.formalism.tcfa.TCFA;
import hu.bme.mit.theta.formalism.tcfa.TcfaEdge;
import hu.bme.mit.theta.formalism.tcfa.TcfaLoc;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;

public class TcfaNetworkPredTest {

	@Test
	public void test() {
		final int n = 2;
		final VarDecl<IntType> vlock = Var("lock", Int());
		final Expr<IntType> lock = vlock.getRef();
		final TCFA fischer = TcfaNetworkTestHelper.fischer(n, vlock);

		final Solver solver = Z3SolverFactory.getInstace().createSolver();

		final TcfaAnalyis<CompositeState<ZoneState, PredState>, CompositePrecision<ZonePrecision, PredPrecision>> analysis = TcfaAnalyis
				.create(fischer, fischer.getInitLoc(),
						CompositeAnalysis.create(TcfaZoneAnalysis.getInstance(), TcfaPredAnalysis.create(solver)));

		final CompositePrecision<ZonePrecision, PredPrecision> subPrecision = CompositePrecision.create(
				ZonePrecision.create(fischer.getClockVars()),
				SimplePredPrecision.create(Arrays.asList(Eq(lock, Int(0)), Eq(lock, Int(1))), solver));
		final LocPrecision<CompositePrecision<ZonePrecision, PredPrecision>, TcfaLoc, TcfaEdge> precision = LocPrecision
				.create(l -> subPrecision);

		final Abstractor<LocState<CompositeState<ZoneState, PredState>, TcfaLoc, TcfaEdge>, TcfaAction, LocPrecision<CompositePrecision<ZonePrecision, PredPrecision>, TcfaLoc, TcfaEdge>> abstractor = WaitlistBasedAbstractor
				.create(analysis, s -> false, FifoWaitlist.supplier());

		final ARG<LocState<CompositeState<ZoneState, PredState>, TcfaLoc, TcfaEdge>, TcfaAction> arg = abstractor
				.createArg();
		abstractor.check(arg, precision);

		System.out.println(new GraphvizWriter().writeString(ArgVisualizer.visualize(arg)));
	}

}
