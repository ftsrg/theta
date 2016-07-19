package hu.bme.mit.inf.ttmc.analysis.tcfa.network;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import org.junit.Test;

import hu.bme.mit.inf.ttmc.analysis.algorithm.Abstractor;
import hu.bme.mit.inf.ttmc.analysis.algorithm.ArgPrinter;
import hu.bme.mit.inf.ttmc.analysis.algorithm.impl.ARG;
import hu.bme.mit.inf.ttmc.analysis.algorithm.impl.AbstractorImpl;
import hu.bme.mit.inf.ttmc.analysis.composite.CompositeDomain;
import hu.bme.mit.inf.ttmc.analysis.composite.CompositeInitFunction;
import hu.bme.mit.inf.ttmc.analysis.composite.CompositePrecision;
import hu.bme.mit.inf.ttmc.analysis.composite.CompositeState;
import hu.bme.mit.inf.ttmc.analysis.composite.CompositeTransferFunction;
import hu.bme.mit.inf.ttmc.analysis.expl.ExplDomain;
import hu.bme.mit.inf.ttmc.analysis.expl.ExplPrecision;
import hu.bme.mit.inf.ttmc.analysis.expl.ExplState;
import hu.bme.mit.inf.ttmc.analysis.expl.GlobalExplPrecision;
import hu.bme.mit.inf.ttmc.analysis.tcfa.TCFAAction;
import hu.bme.mit.inf.ttmc.analysis.tcfa.TCFAAnalysisContext;
import hu.bme.mit.inf.ttmc.analysis.tcfa.TCFADomain;
import hu.bme.mit.inf.ttmc.analysis.tcfa.TCFAInitFunction;
import hu.bme.mit.inf.ttmc.analysis.tcfa.TCFALocTargetPredicate;
import hu.bme.mit.inf.ttmc.analysis.tcfa.TCFAState;
import hu.bme.mit.inf.ttmc.analysis.tcfa.TCFATransferFunction;
import hu.bme.mit.inf.ttmc.analysis.tcfa.expl.TCFAExplInitFunction;
import hu.bme.mit.inf.ttmc.analysis.tcfa.expl.TCFAExplTransferFunction;
import hu.bme.mit.inf.ttmc.analysis.tcfa.zone.TCFAZoneInitFunction;
import hu.bme.mit.inf.ttmc.analysis.tcfa.zone.TCFAZoneTransferFunction;
import hu.bme.mit.inf.ttmc.analysis.zone.ZoneDomain;
import hu.bme.mit.inf.ttmc.analysis.zone.ZonePrecision;
import hu.bme.mit.inf.ttmc.analysis.zone.ZoneState;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFA;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFALoc;
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

		final List<TCFALoc> initLocs = Arrays.asList(eth.getInitLoc(), faultModel.getInitLoc(), fieldLG.getInitLoc(), controlLG.getInitLoc());

		final TCFAAnalysisContext context = new TCFAAnalysisContext();

		final SolverManager manager = new Z3SolverManager();
		final Solver solver = manager.createSolver(true, true);

		final TCFADomain<CompositeState<ZoneState, ExplState>> domain = new TCFADomain<>(
				new CompositeDomain<>(ZoneDomain.getInstance(), ExplDomain.getInstance()));

		final TCFAInitFunction<CompositeState<ZoneState, ExplState>, CompositePrecision<ZonePrecision, ExplPrecision>> initFunction = new TCFAInitFunction<>(
				TCFANetworkLoc.create(initLocs), new CompositeInitFunction<>(new TCFAZoneInitFunction(), new TCFAExplInitFunction()));

		final TCFATransferFunction<CompositeState<ZoneState, ExplState>, CompositePrecision<ZonePrecision, ExplPrecision>> transferFunction = new TCFATransferFunction<>(
				new CompositeTransferFunction<>(new TCFAZoneTransferFunction(), new TCFAExplTransferFunction(solver)));

		final TCFALocTargetPredicate targetPredicate = new TCFALocTargetPredicate(loc -> false);

		final CompositePrecision<ZonePrecision, ExplPrecision> precision = CompositePrecision.create(
				ZonePrecision.builder().addAll(prosigma.getClocks()).build(),
				GlobalExplPrecision.create(Collections.singleton(prosigma.getChan()), Collections.emptySet()));

		final Abstractor<TCFAState<CompositeState<ZoneState, ExplState>>, TCFAAction, CompositePrecision<ZonePrecision, ExplPrecision>> abstractor = new AbstractorImpl<>(
				context, domain, initFunction, transferFunction, targetPredicate);

		abstractor.init(precision);
		abstractor.check(precision);

		final ARG<?, ?> arg = abstractor.getARG();

		System.out.println(ArgPrinter.toGraphvizString(arg));

	}

}
