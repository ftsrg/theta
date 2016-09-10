package hu.bme.mit.theta.analysis.tcfa.pred;

import static hu.bme.mit.theta.core.expr.impl.Exprs.Eq;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Int;
import static hu.bme.mit.theta.core.type.impl.Types.Int;
import static hu.bme.mit.theta.formalism.common.decl.impl.Decls2.Var;

import java.util.Collections;

import org.junit.Ignore;
import org.junit.Test;

import hu.bme.mit.theta.analysis.algorithm.Abstractor;
import hu.bme.mit.theta.analysis.algorithm.ArgPrinter;
import hu.bme.mit.theta.analysis.algorithm.impl.AbstractorImpl;
import hu.bme.mit.theta.analysis.pred.GlobalPredPrecision;
import hu.bme.mit.theta.analysis.pred.PredPrecision;
import hu.bme.mit.theta.analysis.pred.PredState;
import hu.bme.mit.theta.analysis.tcfa.TcfaAction;
import hu.bme.mit.theta.analysis.tcfa.TcfaAnalyis;
import hu.bme.mit.theta.analysis.tcfa.TcfaState;
import hu.bme.mit.theta.analysis.tcfa.pred.TcfaPredAnalysis;
import hu.bme.mit.theta.core.type.IntType;
import hu.bme.mit.theta.formalism.common.decl.VarDecl;
import hu.bme.mit.theta.formalism.tcfa.instances.FischerTCFA;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverManager;
import hu.bme.mit.theta.solver.z3.Z3SolverManager;

public class TcfaPredTest {

	@Test
	@Ignore
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
