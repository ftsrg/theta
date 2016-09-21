package hu.bme.mit.theta.analysis.tcfa.expl;

import static hu.bme.mit.theta.core.decl.impl.Decls.Var;
import static hu.bme.mit.theta.core.type.impl.Types.Int;

import java.util.Collections;

import org.junit.Ignore;
import org.junit.Test;

import hu.bme.mit.theta.analysis.algorithm.ArgPrinter;
import hu.bme.mit.theta.analysis.algorithm.cegar.Abstractor;
import hu.bme.mit.theta.analysis.algorithm.cegar.AbstractorImpl;
import hu.bme.mit.theta.analysis.expl.ExplPrecision;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.tcfa.TcfaAction;
import hu.bme.mit.theta.analysis.tcfa.TcfaAnalyis;
import hu.bme.mit.theta.analysis.tcfa.TcfaState;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.IntType;
import hu.bme.mit.theta.formalism.tcfa.instances.FischerTCFA;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverManager;
import hu.bme.mit.theta.solver.z3.Z3SolverManager;

public class TcfaExplTest {

	@Test
	@Ignore
	public void test() {
		final VarDecl<IntType> vlock = Var("lock", Int());
		final FischerTCFA fischer = new FischerTCFA(1, 1, 2, vlock);

		final SolverManager manager = new Z3SolverManager();
		final Solver solver = manager.createSolver(true, true);

		final TcfaAnalyis<ExplState, ExplPrecision> analyis = TcfaAnalyis.create(fischer.getInitial(),
				TcfaExplAnalysis.create(solver));

		final ExplPrecision precision = ExplPrecision.create(Collections.singleton(vlock));

		final Abstractor<TcfaState<ExplState>, TcfaAction, ExplPrecision> abstractor = new AbstractorImpl<>(analyis,
				s -> s.getLoc().equals(fischer.getCritical()));

		abstractor.init(precision);
		abstractor.check(precision);

		System.out.println(ArgPrinter.toGraphvizString(abstractor.getARG()));

		System.out.println("\n\nCounterexample(s):");
		System.out.println(abstractor.getARG().getCounterexamples());
	}

}
