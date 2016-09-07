package hu.bme.mit.inf.theta.analysis.tcfa.composite;

import static hu.bme.mit.inf.theta.core.type.impl.Types.Int;
import static hu.bme.mit.inf.theta.formalism.common.decl.impl.Decls2.Var;

import java.util.Collections;
import java.util.HashMap;

import org.junit.Ignore;
import org.junit.Test;

import hu.bme.mit.inf.theta.analysis.algorithm.Abstractor;
import hu.bme.mit.inf.theta.analysis.algorithm.ArgPrinter;
import hu.bme.mit.inf.theta.analysis.algorithm.impl.AbstractorImpl;
import hu.bme.mit.inf.theta.analysis.composite.CompositeAnalysis;
import hu.bme.mit.inf.theta.analysis.composite.CompositePrecision;
import hu.bme.mit.inf.theta.analysis.composite.CompositeState;
import hu.bme.mit.inf.theta.analysis.expl.ExplPrecision;
import hu.bme.mit.inf.theta.analysis.expl.ExplState;
import hu.bme.mit.inf.theta.analysis.expl.GlobalExplPrecision;
import hu.bme.mit.inf.theta.analysis.tcfa.TcfaAction;
import hu.bme.mit.inf.theta.analysis.tcfa.TcfaAnalyis;
import hu.bme.mit.inf.theta.analysis.tcfa.TcfaState;
import hu.bme.mit.inf.theta.analysis.tcfa.expl.TcfaExplAnalysis;
import hu.bme.mit.inf.theta.analysis.tcfa.zone.TcfaZoneAnalysis;
import hu.bme.mit.inf.theta.analysis.zone.ZonePrecision;
import hu.bme.mit.inf.theta.analysis.zone.ZoneState;
import hu.bme.mit.inf.theta.core.type.IntType;
import hu.bme.mit.inf.theta.formalism.common.decl.ClockDecl;
import hu.bme.mit.inf.theta.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.theta.formalism.tcfa.instances.FischerTCFA;
import hu.bme.mit.inf.theta.solver.Solver;
import hu.bme.mit.inf.theta.solver.SolverManager;
import hu.bme.mit.inf.theta.solver.z3.Z3SolverManager;

public class TcfaCompositeTest {

	@Test
	@Ignore
	public void testExplicit() {
		final VarDecl<IntType> vlock = Var("lock", Int());
		final FischerTCFA fischer = new FischerTCFA(1, 1, 2, vlock);

		final SolverManager manager = new Z3SolverManager();
		final Solver solver = manager.createSolver(true, true);

		final TcfaAnalyis<CompositeState<ZoneState, ExplState>, CompositePrecision<ZonePrecision, ExplPrecision>> analysis = new TcfaAnalyis<>(
				fischer.getInitial(),
				new CompositeAnalysis<>(TcfaZoneAnalysis.getInstance(), new TcfaExplAnalysis(solver)));

		final HashMap<ClockDecl, Integer> ceilings = new HashMap<>();
		ceilings.put(fischer.getClock(), 2);

		final CompositePrecision<ZonePrecision, ExplPrecision> precision = CompositePrecision
				.create(new ZonePrecision(ceilings), GlobalExplPrecision.create(Collections.singleton(vlock)));

		final Abstractor<TcfaState<CompositeState<ZoneState, ExplState>>, TcfaAction, CompositePrecision<ZonePrecision, ExplPrecision>> abstractor = new AbstractorImpl<>(
				analysis, s -> s.getLoc().equals(fischer.getCritical()));

		abstractor.init(precision);
		abstractor.check(precision);

		System.out.println(ArgPrinter.toGraphvizString(abstractor.getARG()));
	}

}
