package hu.bme.mit.theta.analysis.tcfa.network;

import static hu.bme.mit.theta.core.type.impl.Types.Int;
import static hu.bme.mit.theta.formalism.common.decl.impl.Decls2.Var;
import static java.util.stream.Collectors.toList;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;

import org.junit.Ignore;
import org.junit.Test;

import hu.bme.mit.theta.analysis.algorithm.Abstractor;
import hu.bme.mit.theta.analysis.algorithm.ArgPrinter;
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
import hu.bme.mit.theta.core.type.IntType;
import hu.bme.mit.theta.formalism.common.decl.ClockDecl;
import hu.bme.mit.theta.formalism.common.decl.VarDecl;
import hu.bme.mit.theta.formalism.tcfa.TcfaLoc;
import hu.bme.mit.theta.formalism.tcfa.impl.NetworkTcfaLoc;
import hu.bme.mit.theta.formalism.tcfa.instances.FischerTCFA;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverManager;
import hu.bme.mit.theta.solver.z3.Z3SolverManager;

public class TcfaNetworkExplTest {

	@Test
	@Ignore
	public void test() {
		final int n = 2;

		final VarDecl<IntType> vlock = Var("lock", Int());

		final HashMap<ClockDecl, Integer> ceilings = new HashMap<>();

		final List<FischerTCFA> network = new ArrayList<>(n);
		for (int i = 0; i < n; i++) {
			final FischerTCFA fischer = new FischerTCFA(i + 1, 1, 2, vlock);
			ceilings.put(fischer.getClock(), 2);
			network.add(fischer);
		}

		final List<TcfaLoc> initLocs = network.stream().map(comp -> comp.getInitial()).collect(toList());

		////

		final SolverManager manager = new Z3SolverManager();
		final Solver solver = manager.createSolver(true, true);

		final TcfaAnalyis<CompositeState<ZoneState, ExplState>, CompositePrecision<ZonePrecision, ExplPrecision>> analysis = new TcfaAnalyis<>(
				new NetworkTcfaLoc(initLocs),
				new CompositeAnalysis<>(TcfaZoneAnalysis.getInstance(), new TcfaExplAnalysis(solver)));

		final CompositePrecision<ZonePrecision, ExplPrecision> precision = CompositePrecision
				.create(new ZonePrecision(ceilings), GlobalExplPrecision.create(Collections.singleton(vlock)));

		final Abstractor<TcfaState<CompositeState<ZoneState, ExplState>>, TcfaAction, CompositePrecision<ZonePrecision, ExplPrecision>> abstractor = new AbstractorImpl<>(
				analysis, s -> false);

		abstractor.init(precision);
		abstractor.check(precision);

		System.out.println(ArgPrinter.toGraphvizString(abstractor.getARG()));
	}

}
