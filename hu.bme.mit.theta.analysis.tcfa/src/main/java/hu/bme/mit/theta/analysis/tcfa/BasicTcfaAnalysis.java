package hu.bme.mit.theta.analysis.tcfa;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.ActionFunction;
import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.InitFunction;
import hu.bme.mit.theta.analysis.TransferFunction;
import hu.bme.mit.theta.analysis.automaton.AutomatonPrecision;
import hu.bme.mit.theta.analysis.automaton.AutomatonState;
import hu.bme.mit.theta.analysis.composite.CompositeAnalysis;
import hu.bme.mit.theta.analysis.composite.CompositePrecision;
import hu.bme.mit.theta.analysis.composite.CompositeState;
import hu.bme.mit.theta.analysis.expl.ExplPrecision;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.impl.FixedPrecisionAnalysis;
import hu.bme.mit.theta.analysis.impl.NullPrecision;
import hu.bme.mit.theta.analysis.tcfa.expl.TcfaExplAnalysis;
import hu.bme.mit.theta.analysis.tcfa.zone.TcfaZoneAnalysis;
import hu.bme.mit.theta.analysis.zone.ZonePrecision;
import hu.bme.mit.theta.analysis.zone.ZoneState;
import hu.bme.mit.theta.formalism.tcfa.TCFA;
import hu.bme.mit.theta.formalism.tcfa.TcfaEdge;
import hu.bme.mit.theta.formalism.tcfa.TcfaLoc;
import hu.bme.mit.theta.solver.Solver;

public final class BasicTcfaAnalysis implements
		Analysis<AutomatonState<CompositeState<ZoneState, ExplState>, TcfaLoc, TcfaEdge>, TcfaAction, NullPrecision> {

	private final Analysis<AutomatonState<CompositeState<ZoneState, ExplState>, TcfaLoc, TcfaEdge>, TcfaAction, NullPrecision> analysis;

	private BasicTcfaAnalysis(final TCFA tcfa, final Solver solver) {
		checkNotNull(tcfa);
		checkNotNull(solver);

		final Analysis<AutomatonState<CompositeState<ZoneState, ExplState>, TcfaLoc, TcfaEdge>, TcfaAction, AutomatonPrecision<CompositePrecision<ZonePrecision, ExplPrecision>, TcfaLoc, TcfaEdge>> componentAnalysis = TcfaAnalyis
				.create(tcfa.getInitLoc(),
						CompositeAnalysis.create(TcfaZoneAnalysis.getInstance(), TcfaExplAnalysis.create(solver)));

		final CompositePrecision<ZonePrecision, ExplPrecision> precision = CompositePrecision
				.create(ZonePrecision.create(tcfa.getClockVars()), ExplPrecision.create(tcfa.getDataVars()));

		final AutomatonPrecision<CompositePrecision<ZonePrecision, ExplPrecision>, TcfaLoc, TcfaEdge> fixedPrecision = AutomatonPrecision
				.create(l -> precision);

		analysis = FixedPrecisionAnalysis.create(componentAnalysis, fixedPrecision);
	}

	public static BasicTcfaAnalysis create(final TCFA tcfa, final Solver solver) {
		return new BasicTcfaAnalysis(tcfa, solver);
	}

	@Override
	public Domain<AutomatonState<CompositeState<ZoneState, ExplState>, TcfaLoc, TcfaEdge>> getDomain() {
		return analysis.getDomain();
	}

	@Override
	public InitFunction<AutomatonState<CompositeState<ZoneState, ExplState>, TcfaLoc, TcfaEdge>, NullPrecision> getInitFunction() {
		return analysis.getInitFunction();
	}

	@Override
	public TransferFunction<AutomatonState<CompositeState<ZoneState, ExplState>, TcfaLoc, TcfaEdge>, TcfaAction, NullPrecision> getTransferFunction() {
		return analysis.getTransferFunction();
	}

	@Override
	public ActionFunction<? super AutomatonState<CompositeState<ZoneState, ExplState>, TcfaLoc, TcfaEdge>, ? extends TcfaAction> getActionFunction() {
		return analysis.getActionFunction();
	}

}
