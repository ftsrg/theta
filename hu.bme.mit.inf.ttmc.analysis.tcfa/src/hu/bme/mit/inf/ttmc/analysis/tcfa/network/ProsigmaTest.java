package hu.bme.mit.inf.ttmc.analysis.tcfa.network;

import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Int;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;

import org.junit.Test;

import hu.bme.mit.inf.ttmc.analysis.algorithm.Abstractor;
import hu.bme.mit.inf.ttmc.analysis.algorithm.ArgPrinter;
import hu.bme.mit.inf.ttmc.analysis.algorithm.impl.ARG;
import hu.bme.mit.inf.ttmc.analysis.algorithm.impl.AbstractorImpl;
import hu.bme.mit.inf.ttmc.analysis.composite.CompositeAnalysis;
import hu.bme.mit.inf.ttmc.analysis.composite.CompositePrecision;
import hu.bme.mit.inf.ttmc.analysis.composite.CompositeState;
import hu.bme.mit.inf.ttmc.analysis.expl.ExplPrecision;
import hu.bme.mit.inf.ttmc.analysis.expl.ExplState;
import hu.bme.mit.inf.ttmc.analysis.expl.GlobalExplPrecision;
import hu.bme.mit.inf.ttmc.analysis.tcfa.TcfaAction;
import hu.bme.mit.inf.ttmc.analysis.tcfa.TcfaAnalyis;
import hu.bme.mit.inf.ttmc.analysis.tcfa.TcfaState;
import hu.bme.mit.inf.ttmc.analysis.tcfa.expl.TcfaExplAnalysis;
import hu.bme.mit.inf.ttmc.analysis.tcfa.zone.TcfaZoneAnalysis;
import hu.bme.mit.inf.ttmc.analysis.zone.ZonePrecision;
import hu.bme.mit.inf.ttmc.analysis.zone.ZoneState;
import hu.bme.mit.inf.ttmc.formalism.common.decl.ClockDecl;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFA;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TcfaLoc;
import hu.bme.mit.inf.ttmc.formalism.tcfa.dsl.TcfaDslManager;
import hu.bme.mit.inf.ttmc.formalism.tcfa.dsl.TcfaSpec;
import hu.bme.mit.inf.ttmc.formalism.tcfa.impl.NetworkTcfaLoc;
import hu.bme.mit.inf.ttmc.formalism.tcfa.instances.ProsigmaTCFA;
import hu.bme.mit.inf.ttmc.solver.Solver;
import hu.bme.mit.inf.ttmc.solver.SolverManager;
import hu.bme.mit.inf.ttmc.solver.z3.Z3SolverManager;

public class ProsigmaTest {

	@Test
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
