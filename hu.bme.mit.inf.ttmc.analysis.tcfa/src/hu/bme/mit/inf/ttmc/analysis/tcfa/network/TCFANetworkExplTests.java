package hu.bme.mit.inf.ttmc.analysis.tcfa.network;

import static hu.bme.mit.inf.ttmc.core.type.impl.Types.Int;
import static hu.bme.mit.inf.ttmc.formalism.common.decl.impl.Decls2.Var;
import static java.util.stream.Collectors.toList;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;

import org.junit.Test;

import hu.bme.mit.inf.ttmc.analysis.algorithm.Abstractor;
import hu.bme.mit.inf.ttmc.analysis.algorithm.ArgPrinter;
import hu.bme.mit.inf.ttmc.analysis.algorithm.impl.AbstractorImpl;
import hu.bme.mit.inf.ttmc.analysis.composite.CompositeAnalysis;
import hu.bme.mit.inf.ttmc.analysis.composite.CompositePrecision;
import hu.bme.mit.inf.ttmc.analysis.composite.CompositeState;
import hu.bme.mit.inf.ttmc.analysis.expl.ExplPrecision;
import hu.bme.mit.inf.ttmc.analysis.expl.ExplState;
import hu.bme.mit.inf.ttmc.analysis.expl.GlobalExplPrecision;
import hu.bme.mit.inf.ttmc.analysis.tcfa.TCFAAction;
import hu.bme.mit.inf.ttmc.analysis.tcfa.TCFAAnalyis;
import hu.bme.mit.inf.ttmc.analysis.tcfa.TCFAState;
import hu.bme.mit.inf.ttmc.analysis.tcfa.expl.TCFAExplAnalysis;
import hu.bme.mit.inf.ttmc.analysis.tcfa.zone.TCFAZoneAnalysis;
import hu.bme.mit.inf.ttmc.analysis.zone.ZonePrecision;
import hu.bme.mit.inf.ttmc.analysis.zone.ZoneState;
import hu.bme.mit.inf.ttmc.core.type.IntType;
import hu.bme.mit.inf.ttmc.formalism.common.decl.ClockDecl;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TcfaLoc;
import hu.bme.mit.inf.ttmc.formalism.tcfa.impl.NetworkTcfaLoc;
import hu.bme.mit.inf.ttmc.formalism.tcfa.instances.FischerTCFA;
import hu.bme.mit.inf.ttmc.solver.Solver;
import hu.bme.mit.inf.ttmc.solver.SolverManager;
import hu.bme.mit.inf.ttmc.solver.z3.Z3SolverManager;

public class TCFANetworkExplTests {

	@Test
	public void test() {
		final int n = 6;

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

		final TCFAAnalyis<CompositeState<ZoneState, ExplState>, CompositePrecision<ZonePrecision, ExplPrecision>> analysis = new TCFAAnalyis<>(
				new NetworkTcfaLoc(initLocs),
				new CompositeAnalysis<>(TCFAZoneAnalysis.getInstance(), new TCFAExplAnalysis(solver)));

		final CompositePrecision<ZonePrecision, ExplPrecision> precision = CompositePrecision.create(
				new ZonePrecision(ceilings),
				GlobalExplPrecision.create(Collections.singleton(vlock), Collections.emptySet()));

		final Abstractor<TCFAState<CompositeState<ZoneState, ExplState>>, TCFAAction, CompositePrecision<ZonePrecision, ExplPrecision>> abstractor = new AbstractorImpl<>(
				analysis, s -> false);

		abstractor.init(precision);
		abstractor.check(precision);

		System.out.println(ArgPrinter.toGraphvizString(abstractor.getARG()));
	}

}
