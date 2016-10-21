package hu.bme.mit.theta.analysis.tcfa.pred;

import static hu.bme.mit.theta.core.decl.impl.Decls.Var;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Eq;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Int;
import static hu.bme.mit.theta.core.type.impl.Types.Int;

import java.util.Collections;

import org.junit.Test;

import hu.bme.mit.theta.analysis.algorithm.cegar.Abstractor;
import hu.bme.mit.theta.analysis.algorithm.cegar.AbstractorStatus;
import hu.bme.mit.theta.analysis.algorithm.cegar.WaitlistBasedAbstractor;
import hu.bme.mit.theta.analysis.loc.LocPrecision;
import hu.bme.mit.theta.analysis.loc.LocState;
import hu.bme.mit.theta.analysis.pred.PredPrecision;
import hu.bme.mit.theta.analysis.pred.PredState;
import hu.bme.mit.theta.analysis.pred.SimplePredPrecision;
import hu.bme.mit.theta.analysis.tcfa.TcfaAction;
import hu.bme.mit.theta.analysis.tcfa.TcfaAnalyis;
import hu.bme.mit.theta.analysis.utils.ArgVisualizer;
import hu.bme.mit.theta.common.visualization.GraphvizWriter;
import hu.bme.mit.theta.common.waitlist.LifoWaitlist;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.IntType;
import hu.bme.mit.theta.formalism.tcfa.TcfaEdge;
import hu.bme.mit.theta.formalism.tcfa.TcfaLoc;
import hu.bme.mit.theta.formalism.tcfa.instances.FischerTcfa;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;

public class TcfaPredTest {

	@Test
	public void test() {
		final VarDecl<IntType> vlock = Var("lock", Int());
		final FischerTcfa fischer = new FischerTcfa(1, 1, 2, vlock);

		final Solver solver = Z3SolverFactory.getInstace().createSolver();

		final TcfaAnalyis<PredState, PredPrecision> analysis = TcfaAnalyis.create(fischer.getInitial(),
				TcfaPredAnalysis.create(solver));

		final PredPrecision subPrecision = SimplePredPrecision.create(Collections.singleton(Eq(vlock.getRef(), Int(0))),
				solver);
		final LocPrecision<PredPrecision, TcfaLoc, TcfaEdge> precision = LocPrecision.create(l -> subPrecision);

		final Abstractor<LocState<PredState, TcfaLoc, TcfaEdge>, TcfaAction, LocPrecision<PredPrecision, TcfaLoc, TcfaEdge>> abstractor = WaitlistBasedAbstractor
				.create(analysis, s -> s.getLoc().equals(fischer.getCritical()), new LifoWaitlist<>());

		final AbstractorStatus<?, ?> abstractorStatus = abstractor.initAndCheck(precision);

		System.out.println(new GraphvizWriter().writeString(ArgVisualizer.visualize(abstractorStatus.getArg())));

		System.out.println("\n\nCounterexample(s):");
		System.out.println(abstractorStatus.getArg().getAllCexs());

	}

}
