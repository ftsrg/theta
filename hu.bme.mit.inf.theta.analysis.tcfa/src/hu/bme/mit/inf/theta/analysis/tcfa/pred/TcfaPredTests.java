package hu.bme.mit.inf.theta.analysis.tcfa.pred;

import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.Eq;
import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.Int;
import static hu.bme.mit.inf.theta.core.type.impl.Types.Int;
import static hu.bme.mit.inf.theta.formalism.common.decl.impl.Decls2.Var;

import java.util.Collections;

import org.junit.Test;

import hu.bme.mit.inf.theta.analysis.algorithm.Abstractor;
import hu.bme.mit.inf.theta.analysis.algorithm.ArgPrinter;
import hu.bme.mit.inf.theta.analysis.algorithm.impl.AbstractorImpl;
import hu.bme.mit.inf.theta.analysis.pred.GlobalPredPrecision;
import hu.bme.mit.inf.theta.analysis.pred.PredPrecision;
import hu.bme.mit.inf.theta.analysis.pred.PredState;
import hu.bme.mit.inf.theta.analysis.tcfa.TcfaAction;
import hu.bme.mit.inf.theta.analysis.tcfa.TcfaAnalyis;
import hu.bme.mit.inf.theta.analysis.tcfa.TcfaState;
import hu.bme.mit.inf.theta.core.type.IntType;
import hu.bme.mit.inf.theta.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.theta.formalism.tcfa.instances.FischerTCFA;
import hu.bme.mit.inf.theta.solver.Solver;
import hu.bme.mit.inf.theta.solver.SolverManager;
import hu.bme.mit.inf.theta.solver.z3.Z3SolverManager;

public class TcfaPredTests {

	@Test
	public void test() {
		final VarDecl<IntType> vlock = Var("lock", Int());
		final FischerTCFA fischer = new FischerTCFA(1, 1, 2, vlock);

		final SolverManager manager = new Z3SolverManager();
		final Solver solver = manager.createSolver(true, true);

		final TcfaAnalyis<PredState, PredPrecision> analysis = new TcfaAnalyis<>(fischer.getInitial(),
				new TcfaPredAnalysis(solver));

		final PredPrecision precision = GlobalPredPrecision.create(Collections.singleton(Eq(vlock.getRef(), Int(0))));

		final Abstractor<TcfaState<PredState>, TcfaAction, PredPrecision> abstractor = new AbstractorImpl<>(analysis,
				s -> s.getLoc().equals(fischer.getCritical()));

		abstractor.init(precision);
		abstractor.check(precision);

		System.out.println(ArgPrinter.toGraphvizString(abstractor.getARG()));

		System.out.println("\n\nCounterexample(s):");
		System.out.println(abstractor.getARG().getCounterexamples());

	}

}
