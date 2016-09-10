package hu.bme.mit.theta.analysis.tcfa.network;

import static hu.bme.mit.theta.core.expr.impl.Exprs.Int;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;

import org.junit.Ignore;
import org.junit.Test;

import hu.bme.mit.theta.analysis.algorithm.Abstractor;
import hu.bme.mit.theta.analysis.algorithm.ArgPrinter;
import hu.bme.mit.theta.analysis.algorithm.impl.ARG;
import hu.bme.mit.theta.analysis.algorithm.impl.AbstractorImpl;
import hu.bme.mit.theta.analysis.composite.CompositeAnalysis;
import hu.bme.mit.theta.analysis.composite.CompositePrecision;
import hu.bme.mit.theta.analysis.composite.CompositeState;
import hu.bme.mit.theta.analysis.expl.ExplPrecision;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.expl.GlobalExplPrecision;
import hu.bme.mit.theta.analysis.tcfa.TcfaAction;
import hu.bme.mit.theta.analysis.tcfa.TcfaAnalyis;
import hu.bme.mit.theta.analysis.tcfa.TcfaState;
import hu.bme.mit.theta.analysis.tcfa.expl.TcfaExplAnalysis;
import hu.bme.mit.theta.analysis.tcfa.zone.TcfaZoneAnalysis;
import hu.bme.mit.theta.analysis.zone.ZonePrecision;
import hu.bme.mit.theta.analysis.zone.ZoneState;
import hu.bme.mit.theta.formalism.common.decl.ClockDecl;
import hu.bme.mit.theta.formalism.tcfa.TCFA;
import hu.bme.mit.theta.formalism.tcfa.TcfaLoc;
import hu.bme.mit.theta.formalism.tcfa.dsl.TcfaDslManager;
import hu.bme.mit.theta.formalism.tcfa.dsl.TcfaSpec;
import hu.bme.mit.theta.formalism.tcfa.impl.NetworkTcfaLoc;
import hu.bme.mit.theta.formalism.tcfa.instances.ProsigmaTCFA;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverManager;
import hu.bme.mit.theta.solver.z3.Z3SolverManager;

public class ProsigmaTest {

	@Test
	@Ignore
	public void test() {
		final ProsigmaTCFA prosigma = new ProsigmaTCFA(3, 7);

		final TCFA eth = prosigma.getETH();
		final TCFA faultModel = prosigma.getFaultModel();
		final TCFA fieldLG = prosigma.getFieldLG();
		final TCFA controlLG = prosigma.getControlLG();

		final List<TcfaLoc> initLocs = Arrays.asList(eth.getInitLoc(), faultModel.getInitLoc(), fieldLG.getInitLoc(),
				controlLG.getInitLoc());

		final SolverManager manager = new Z3SolverManager();
		final Solver solver = manager.createSolver(true, true);

		final TcfaAnalyis<CompositeState<ZoneState, ExplState>, CompositePrecision<ZonePrecision, ExplPrecision>> analysis = new TcfaAnalyis<>(
				new NetworkTcfaLoc(initLocs),
				new CompositeAnalysis<>(TcfaZoneAnalysis.getInstance(), new TcfaExplAnalysis(solver)));

		final HashMap<ClockDecl, Integer> ceilings = new HashMap<>();
		for (final ClockDecl clock : prosigma.getClocks()) {
			ceilings.put(clock, 7);
		}

		final CompositePrecision<ZonePrecision, ExplPrecision> precision = CompositePrecision.create(
				new ZonePrecision(ceilings), GlobalExplPrecision.create(Collections.singleton(prosigma.getChan())));

		final Abstractor<TcfaState<CompositeState<ZoneState, ExplState>>, TcfaAction, CompositePrecision<ZonePrecision, ExplPrecision>> abstractor = new AbstractorImpl<>(
				analysis, s -> false);

		abstractor.init(precision);
		abstractor.check(precision);

		final ARG<?, ?, ?> arg = abstractor.getARG();

		System.out.println(ArgPrinter.toGraphvizString(arg));

	}

	@Test
	@Ignore
	public void test2() throws FileNotFoundException, IOException {
		final TcfaSpec prosigmaSpec = TcfaDslManager.parse("instances/prosigma.tcfa", Arrays.asList(Int(3), Int(7)));
		final TCFA prosigma = prosigmaSpec.getTcfa("prosigma");

		final SolverManager manager = new Z3SolverManager();
		final Solver solver = manager.createSolver(true, true);

		final TcfaAnalyis<CompositeState<ZoneState, ExplState>, CompositePrecision<ZonePrecision, ExplPrecision>> analysis = new TcfaAnalyis<>(
				prosigma.getInitLoc(),
				new CompositeAnalysis<>(TcfaZoneAnalysis.getInstance(), new TcfaExplAnalysis(solver)));

		final HashMap<ClockDecl, Integer> ceilings = new HashMap<>();
		for (final ClockDecl clock : prosigma.getClockVars()) {
			ceilings.put(clock, 7);
		}

		final CompositePrecision<ZonePrecision, ExplPrecision> precision = CompositePrecision
				.create(new ZonePrecision(ceilings), GlobalExplPrecision.create(prosigma.getDataVars()));

		final Abstractor<TcfaState<CompositeState<ZoneState, ExplState>>, TcfaAction, CompositePrecision<ZonePrecision, ExplPrecision>> abstractor = new AbstractorImpl<>(
				analysis, s -> false);

		abstractor.init(precision);
		abstractor.check(precision);

		final ARG<?, ?, ?> arg = abstractor.getARG();

		System.out.println(ArgPrinter.toGraphvizString(arg));
	}

}
