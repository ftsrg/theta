package hu.bme.mit.theta.analysis.tcfa.composite;

import static hu.bme.mit.theta.core.expr.impl.Exprs.Int;

import java.io.FileNotFoundException;
import java.io.IOException;

import org.junit.Ignore;
import org.junit.Test;

import hu.bme.mit.theta.analysis.algorithm.ArgPrinter;
import hu.bme.mit.theta.analysis.algorithm.cegar.Abstractor;
import hu.bme.mit.theta.analysis.algorithm.cegar.AbstractorImpl;
import hu.bme.mit.theta.analysis.composite.CompositeState;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.impl.NullPrecision;
import hu.bme.mit.theta.analysis.tcfa.BasicTcfaAnalysis;
import hu.bme.mit.theta.analysis.tcfa.TcfaAction;
import hu.bme.mit.theta.analysis.tcfa.TcfaState;
import hu.bme.mit.theta.analysis.zone.ZoneState;
import hu.bme.mit.theta.formalism.tcfa.TCFA;
import hu.bme.mit.theta.formalism.tcfa.dsl.TcfaDslManager;
import hu.bme.mit.theta.formalism.tcfa.dsl.TcfaSpec;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverManager;
import hu.bme.mit.theta.solver.z3.Z3SolverManager;

public class TcfaCompositeTest {

	@Test
	@Ignore
	public void testExplicit() throws FileNotFoundException, IOException {
		final TcfaSpec spec = TcfaDslManager.parse("src/test/resources/fischer.tcfa", Int(1), Int(2));
		final TCFA fischers = spec.getTcfa("fischers");

		final SolverManager manager = new Z3SolverManager();
		final Solver solver = manager.createSolver();

		final BasicTcfaAnalysis analysis = BasicTcfaAnalysis.create(fischers, solver);

		final Abstractor<TcfaState<CompositeState<ZoneState, ExplState>>, TcfaAction, NullPrecision> abstractor = new AbstractorImpl<>(
				analysis, s -> s.getLoc().getName().equals("(crit, crit)"));

		abstractor.init(NullPrecision.getInstance());
		abstractor.check(NullPrecision.getInstance());

		System.out.println(ArgPrinter.toGraphvizString(abstractor.getARG()));
	}

}
