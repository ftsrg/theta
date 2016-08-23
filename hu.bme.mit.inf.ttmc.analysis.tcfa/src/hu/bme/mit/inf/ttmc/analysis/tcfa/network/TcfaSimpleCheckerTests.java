package hu.bme.mit.inf.ttmc.analysis.tcfa.network;

import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Eq;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Int;
import static hu.bme.mit.inf.ttmc.core.type.impl.Types.Int;
import static hu.bme.mit.inf.ttmc.formalism.common.decl.impl.Decls2.Var;
import static java.util.stream.Collectors.toList;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;

import org.junit.Ignore;
import org.junit.Test;

import hu.bme.mit.inf.ttmc.analysis.algorithm.impl.SimpleChecker;
import hu.bme.mit.inf.ttmc.analysis.composite.CompositeAnalysis;
import hu.bme.mit.inf.ttmc.analysis.composite.CompositePrecision;
import hu.bme.mit.inf.ttmc.analysis.composite.CompositeState;
import hu.bme.mit.inf.ttmc.analysis.expl.ExplPrecision;
import hu.bme.mit.inf.ttmc.analysis.expl.ExplState;
import hu.bme.mit.inf.ttmc.analysis.expl.GlobalExplPrecision;
import hu.bme.mit.inf.ttmc.analysis.pred.GlobalPredPrecision;
import hu.bme.mit.inf.ttmc.analysis.pred.PredPrecision;
import hu.bme.mit.inf.ttmc.analysis.pred.PredState;
import hu.bme.mit.inf.ttmc.analysis.tcfa.TcfaAnalyis;
import hu.bme.mit.inf.ttmc.analysis.tcfa.expl.TcfaExplAnalysis;
import hu.bme.mit.inf.ttmc.analysis.tcfa.pred.TcfaPredAnalysis;
import hu.bme.mit.inf.ttmc.analysis.tcfa.zone.TcfaZoneAnalysis;
import hu.bme.mit.inf.ttmc.analysis.zone.ZonePrecision;
import hu.bme.mit.inf.ttmc.analysis.zone.ZoneState;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.IntType;
import hu.bme.mit.inf.ttmc.formalism.common.decl.ClockDecl;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TcfaLoc;
import hu.bme.mit.inf.ttmc.formalism.tcfa.impl.NetworkTcfaLoc;
import hu.bme.mit.inf.ttmc.formalism.tcfa.instances.FischerTCFA;
import hu.bme.mit.inf.ttmc.solver.Solver;
import hu.bme.mit.inf.ttmc.solver.SolverManager;
import hu.bme.mit.inf.ttmc.solver.z3.Z3SolverManager;

public class TcfaSimpleCheckerTests {

	@Test
	@Ignore
	public void testExplicit() {
		final int n = 4;

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

		System.out.println(SimpleChecker.run(analysis, s -> false, precision));
	}

	@Test
	public void testPredicate() {
		final int n = 3;

		final VarDecl<IntType> vlock = Var("lock", Int());
		final Expr<IntType> lock = vlock.getRef();

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

		final TcfaAnalyis<CompositeState<ZoneState, PredState>, CompositePrecision<ZonePrecision, PredPrecision>> analysis = new TcfaAnalyis<>(
				new NetworkTcfaLoc(initLocs),
				new CompositeAnalysis<>(TcfaZoneAnalysis.getInstance(), new TcfaPredAnalysis(solver)));

		final CompositePrecision<ZonePrecision, PredPrecision> precision = CompositePrecision.create(
				new ZonePrecision(ceilings),
				GlobalPredPrecision.create(Arrays.asList(Eq(lock, Int(0)), Eq(lock, Int(1)))));

		System.out.println(SimpleChecker.run(analysis, s -> false, precision));
	}

}
