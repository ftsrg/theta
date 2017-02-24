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
import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.impl.FixedPrecAnalysis;
import hu.bme.mit.theta.analysis.impl.NullPrec;
import hu.bme.mit.theta.analysis.loc.ConstLocPrec;
import hu.bme.mit.theta.analysis.loc.LocAnalysis;
import hu.bme.mit.theta.analysis.loc.LocState;
import hu.bme.mit.theta.analysis.utils.ArgVisualizer;
import hu.bme.mit.theta.analysis.waitlist.FifoWaitlist;
import hu.bme.mit.theta.common.visualization.GraphvizWriter;
import hu.bme.mit.theta.formalism.tcfa.TCFA;
import hu.bme.mit.theta.formalism.tcfa.TcfaEdge;
import hu.bme.mit.theta.formalism.tcfa.TcfaLoc;
import hu.bme.mit.theta.formalism.tcfa.instances.TcfaModels;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;

public class TcfaExplTest {

	@Test
	public void test() {
		final int n = 2;
		final TCFA fischer = TcfaModels.fischer(n, 1, 2);

		final Solver solver = Z3SolverFactory.getInstace().createSolver();

		final TcfaLts lts = TcfaLts.create(fischer);

		final Analysis<LocState<ExplState, TcfaLoc, TcfaEdge>, TcfaAction, NullPrec> analysis = FixedPrecAnalysis
				.create(LocAnalysis.create(fischer.getInitLoc(), ExplAnalysis.create(solver, True())),
						ConstLocPrec.create(ExplPrec.create(fischer.getDataVars())));

		final Predicate<State> target = s -> false;

		final ArgBuilder<LocState<ExplState, TcfaLoc, TcfaEdge>, TcfaAction, NullPrec> argBuilder = ArgBuilder
				.create(lts, analysis, target);

		final Abstractor<LocState<ExplState, TcfaLoc, TcfaEdge>, TcfaAction, NullPrec> abstractor = WaitlistBasedAbstractor
				.create(argBuilder, LocState::getLoc, FifoWaitlist.supplier());

		final ARG<LocState<ExplState, TcfaLoc, TcfaEdge>, TcfaAction> arg = abstractor.createArg();

		abstractor.check(arg, NullPrec.getInstance());

		System.out.println(new GraphvizWriter().writeString(ArgVisualizer.visualize(arg)));
	}

}
