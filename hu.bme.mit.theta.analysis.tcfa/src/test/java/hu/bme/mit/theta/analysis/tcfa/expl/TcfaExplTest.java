package hu.bme.mit.theta.analysis.tcfa.expl;

import static hu.bme.mit.theta.core.decl.impl.Decls.Var;
import static hu.bme.mit.theta.core.type.impl.Types.Int;

import java.util.Collections;

import org.junit.Test;

import hu.bme.mit.theta.analysis.algorithm.LifoWaitlist;
import hu.bme.mit.theta.analysis.algorithm.cegar.Abstractor;
import hu.bme.mit.theta.analysis.algorithm.cegar.WaitlistBasedAbstractor;
import hu.bme.mit.theta.analysis.automaton.AutomatonPrecision;
import hu.bme.mit.theta.analysis.automaton.AutomatonState;
import hu.bme.mit.theta.analysis.expl.ExplPrecision;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.tcfa.TcfaAction;
import hu.bme.mit.theta.analysis.tcfa.TcfaAnalyis;
import hu.bme.mit.theta.analysis.utils.ArgVisualizer;
import hu.bme.mit.theta.common.visualization.GraphVizWriter;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.IntType;
import hu.bme.mit.theta.formalism.tcfa.TcfaEdge;
import hu.bme.mit.theta.formalism.tcfa.TcfaLoc;
import hu.bme.mit.theta.formalism.tcfa.instances.FischerTcfa;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;

public class TcfaExplTest {

	@Test
	public void test() {
		final VarDecl<IntType> vlock = Var("lock", Int());
		final FischerTcfa fischer = new FischerTcfa(1, 1, 2, vlock);

		final Solver solver = Z3SolverFactory.getInstace().createSolver();

		final TcfaAnalyis<ExplState, ExplPrecision> analyis = TcfaAnalyis.create(fischer.getInitial(),
				TcfaExplAnalysis.create(solver));

		final ExplPrecision subPrecision = ExplPrecision.create(Collections.singleton(vlock));
		final AutomatonPrecision<ExplPrecision, TcfaLoc, TcfaEdge> precision = AutomatonPrecision
				.create(l -> subPrecision);

		final Abstractor<AutomatonState<ExplState, TcfaLoc, TcfaEdge>, TcfaAction, AutomatonPrecision<ExplPrecision, TcfaLoc, TcfaEdge>> abstractor = new WaitlistBasedAbstractor<>(
				analyis, s -> s.getLoc().equals(fischer.getCritical()), new LifoWaitlist<>());

		abstractor.init(precision);
		abstractor.check(precision);

		System.out.println(new GraphVizWriter().writeString(ArgVisualizer.visualize(abstractor.getARG())));

		System.out.println("\n\nCounterexample(s):");
		System.out.println(abstractor.getARG().getCounterexamples());
	}

}
