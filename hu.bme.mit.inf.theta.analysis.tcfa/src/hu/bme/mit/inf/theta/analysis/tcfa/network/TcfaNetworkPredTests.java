package hu.bme.mit.inf.theta.analysis.tcfa.network;

import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.Eq;
import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.Int;
import static hu.bme.mit.inf.theta.core.type.impl.Types.Int;
import static hu.bme.mit.inf.theta.formalism.common.decl.impl.Decls2.Var;
import static java.util.stream.Collectors.toList;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;

import org.junit.Test;

import hu.bme.mit.inf.theta.analysis.algorithm.Abstractor;
import hu.bme.mit.inf.theta.analysis.algorithm.ArgPrinter;
import hu.bme.mit.inf.theta.analysis.algorithm.impl.AbstractorImpl;
import hu.bme.mit.inf.theta.analysis.composite.CompositeAnalysis;
import hu.bme.mit.inf.theta.analysis.composite.CompositePrecision;
import hu.bme.mit.inf.theta.analysis.composite.CompositeState;
import hu.bme.mit.inf.theta.analysis.pred.GlobalPredPrecision;
import hu.bme.mit.inf.theta.analysis.pred.PredPrecision;
import hu.bme.mit.inf.theta.analysis.pred.PredState;
import hu.bme.mit.inf.theta.analysis.tcfa.TcfaAction;
import hu.bme.mit.inf.theta.analysis.tcfa.TcfaAnalyis;
import hu.bme.mit.inf.theta.analysis.tcfa.TcfaState;
import hu.bme.mit.inf.theta.analysis.tcfa.pred.TcfaPredAnalysis;
import hu.bme.mit.inf.theta.analysis.tcfa.zone.TcfaZoneAnalysis;
import hu.bme.mit.inf.theta.analysis.zone.ZonePrecision;
import hu.bme.mit.inf.theta.analysis.zone.ZoneState;
import hu.bme.mit.inf.theta.core.expr.Expr;
import hu.bme.mit.inf.theta.core.type.IntType;
import hu.bme.mit.inf.theta.formalism.common.decl.ClockDecl;
import hu.bme.mit.inf.theta.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.theta.formalism.tcfa.TcfaLoc;
import hu.bme.mit.inf.theta.formalism.tcfa.impl.NetworkTcfaLoc;
import hu.bme.mit.inf.theta.formalism.tcfa.instances.FischerTCFA;
import hu.bme.mit.inf.theta.solver.Solver;
import hu.bme.mit.inf.theta.solver.SolverManager;
import hu.bme.mit.inf.theta.solver.z3.Z3SolverManager;

public class TcfaNetworkPredTests {

	@Test
	public void test() {
		final int n = 6;

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

		final Abstractor<TcfaState<CompositeState<ZoneState, PredState>>, TcfaAction, CompositePrecision<ZonePrecision, PredPrecision>> abstractor = new AbstractorImpl<>(
				analysis, s -> false);

		abstractor.init(precision);
		abstractor.check(precision);

		System.out.println(ArgPrinter.toGraphvizString(abstractor.getARG()));
	}

}
