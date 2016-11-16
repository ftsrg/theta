package hu.bme.mit.theta.analysis.tcfa;

import static hu.bme.mit.theta.core.decl.impl.Decls.Var;
import static hu.bme.mit.theta.core.expr.impl.Exprs.True;
import static hu.bme.mit.theta.core.type.impl.Types.Int;

import java.io.FileNotFoundException;
import java.io.IOException;

import org.junit.Test;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.cegar.Abstractor;
import hu.bme.mit.theta.analysis.algorithm.cegar.WaitlistBasedAbstractor;
import hu.bme.mit.theta.analysis.composite.CompositeAnalysis;
import hu.bme.mit.theta.analysis.composite.CompositePrecision;
import hu.bme.mit.theta.analysis.composite.CompositeState;
import hu.bme.mit.theta.analysis.expl.ExplAnalysis;
import hu.bme.mit.theta.analysis.expl.ExplPrecision;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.impl.FixedPrecisionAnalysis;
import hu.bme.mit.theta.analysis.impl.NullPrecision;
import hu.bme.mit.theta.analysis.loc.LocAnalysis;
import hu.bme.mit.theta.analysis.loc.LocPrecision;
import hu.bme.mit.theta.analysis.loc.LocState;
import hu.bme.mit.theta.analysis.tcfa.zone.TcfaZoneAnalysis;
import hu.bme.mit.theta.analysis.utils.ArgVisualizer;
import hu.bme.mit.theta.analysis.zone.ZonePrecision;
import hu.bme.mit.theta.analysis.zone.ZoneState;
import hu.bme.mit.theta.common.visualization.GraphvizWriter;
import hu.bme.mit.theta.common.waitlist.FifoWaitlist;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.IntType;
import hu.bme.mit.theta.formalism.tcfa.TCFA;
import hu.bme.mit.theta.formalism.tcfa.TcfaEdge;
import hu.bme.mit.theta.formalism.tcfa.TcfaLoc;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;

public class TcfaCompositeTest {

	@Test
	public void test() throws FileNotFoundException, IOException {
		final int n = 2;
		final VarDecl<IntType> vlock = Var("lock", Int());
		final TCFA fischer = TcfaTestHelper.fischer(n, vlock);

		final Solver solver = Z3SolverFactory.getInstace().createSolver();

		final TcfaLts lts = TcfaLts.create(fischer);

		final Analysis<LocState<CompositeState<ZoneState, ExplState>, TcfaLoc, TcfaEdge>, TcfaAction, NullPrecision> analysis = FixedPrecisionAnalysis
				.create(LocAnalysis.create(fischer.getInitLoc(),
						CompositeAnalysis.create(TcfaZoneAnalysis.getInstance(), ExplAnalysis.create(solver, True()))),
						LocPrecision.constant(CompositePrecision.create(ZonePrecision.create(fischer.getClockVars()),
								ExplPrecision.create(fischer.getDataVars()))));

		final Abstractor<LocState<CompositeState<ZoneState, ExplState>, TcfaLoc, TcfaEdge>, TcfaAction, NullPrecision> abstractor = WaitlistBasedAbstractor
				.create(lts, analysis, s -> s.getLoc().getName().equals("(crit, crit)"), FifoWaitlist.supplier());

		final ARG<LocState<CompositeState<ZoneState, ExplState>, TcfaLoc, TcfaEdge>, TcfaAction> arg = abstractor
				.createArg();
		abstractor.check(arg, NullPrecision.getInstance());

		System.out.println(new GraphvizWriter().writeString(ArgVisualizer.visualize(arg)));
	}

}
