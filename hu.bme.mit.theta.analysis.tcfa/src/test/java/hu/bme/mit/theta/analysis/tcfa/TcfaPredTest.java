package hu.bme.mit.theta.analysis.tcfa;

import static hu.bme.mit.theta.core.expr.impl.Exprs.Eq;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Int;
import static hu.bme.mit.theta.core.expr.impl.Exprs.True;

import java.util.Collections;
import java.util.function.Predicate;

import org.junit.Test;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgBuilder;
import hu.bme.mit.theta.analysis.algorithm.cegar.Abstractor;
import hu.bme.mit.theta.analysis.algorithm.cegar.WaitlistBasedAbstractor;
import hu.bme.mit.theta.analysis.impl.PrecMappingAnalysis;
import hu.bme.mit.theta.analysis.loc.ConstLocPrec;
import hu.bme.mit.theta.analysis.loc.LocAnalysis;
import hu.bme.mit.theta.analysis.loc.LocPrec;
import hu.bme.mit.theta.analysis.loc.LocState;
import hu.bme.mit.theta.analysis.pred.PredAnalysis;
import hu.bme.mit.theta.analysis.pred.PredPrec;
import hu.bme.mit.theta.analysis.pred.PredState;
import hu.bme.mit.theta.analysis.pred.SimplePredPrec;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.analysis.utils.ArgVisualizer;
import hu.bme.mit.theta.analysis.waitlist.FifoWaitlist;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.common.visualization.GraphvizWriter;
import hu.bme.mit.theta.formalism.tcfa.TCFA;
import hu.bme.mit.theta.formalism.tcfa.TcfaEdge;
import hu.bme.mit.theta.formalism.tcfa.TcfaLoc;
import hu.bme.mit.theta.formalism.tcfa.instances.TcfaModels;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;

public class TcfaPredTest {

	@Test
	public void test() {
		final int n = 2;
		final TCFA fischer = TcfaModels.fischer(n, 2);

		final Solver solver = Z3SolverFactory.getInstace().createSolver();

		final TcfaLts lts = TcfaLts.create(fischer);

		final LocPrec<PredPrec, TcfaLoc, TcfaEdge> fixedPrec = ConstLocPrec.create(SimplePredPrec
				.create(Collections.singleton(Eq(Utils.anyElementOf(fischer.getDataVars()).getRef(), Int(0))), solver));

		final Analysis<LocState<PredState, TcfaLoc, TcfaEdge>, TcfaAction, UnitPrec> analysis = PrecMappingAnalysis
				.create(LocAnalysis.create(fischer.getInitLoc(), PredAnalysis.create(solver, True())), np -> fixedPrec);

		final Predicate<State> target = s -> false;

		final ArgBuilder<LocState<PredState, TcfaLoc, TcfaEdge>, TcfaAction, UnitPrec> argBuilder = ArgBuilder
				.create(lts, analysis, target);

		final Abstractor<LocState<PredState, TcfaLoc, TcfaEdge>, TcfaAction, UnitPrec> abstractor = WaitlistBasedAbstractor
				.create(argBuilder, LocState::getLoc, FifoWaitlist.supplier());

		final ARG<LocState<PredState, TcfaLoc, TcfaEdge>, TcfaAction> arg = abstractor.createArg();

		abstractor.check(arg, UnitPrec.getInstance());

		System.out.println(new GraphvizWriter().writeString(ArgVisualizer.visualize(arg)));
	}

}
