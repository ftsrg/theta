package hu.bme.mit.theta.analysis.tcfa.impact;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.expr.impl.Exprs.True;

import java.util.Collections;
import java.util.function.Predicate;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyStatus;
import hu.bme.mit.theta.analysis.algorithm.impact.ImpactChecker;
import hu.bme.mit.theta.analysis.composite.CompositeAnalysis;
import hu.bme.mit.theta.analysis.composite.CompositePrecision;
import hu.bme.mit.theta.analysis.composite.CompositeState;
import hu.bme.mit.theta.analysis.expl.ExplAnalysis;
import hu.bme.mit.theta.analysis.expl.ExplPrecision;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.impl.FixedPrecisionAnalysis;
import hu.bme.mit.theta.analysis.impl.NullPrecision;
import hu.bme.mit.theta.analysis.loc.LocAnalysis;
import hu.bme.mit.theta.analysis.loc.LocPrecision;
import hu.bme.mit.theta.analysis.loc.LocState;
import hu.bme.mit.theta.analysis.tcfa.TcfaAction;
import hu.bme.mit.theta.analysis.tcfa.TcfaLts;
import hu.bme.mit.theta.analysis.tcfa.zone.TcfaZoneAnalysis;
import hu.bme.mit.theta.analysis.zone.ZonePrecision;
import hu.bme.mit.theta.analysis.zone.ZoneState;
import hu.bme.mit.theta.formalism.tcfa.TCFA;
import hu.bme.mit.theta.formalism.tcfa.TcfaEdge;
import hu.bme.mit.theta.formalism.tcfa.TcfaLoc;
import hu.bme.mit.theta.solver.Solver;

public final class TcfaImpactChecker implements
		SafetyChecker<LocState<CompositeState<ZoneState, ExplState>, TcfaLoc, TcfaEdge>, TcfaAction, NullPrecision> {

	private final ImpactChecker<LocState<CompositeState<ZoneState, ExplState>, TcfaLoc, TcfaEdge>, TcfaAction, NullPrecision> checker;

	private TcfaImpactChecker(final TCFA tcfa, final Solver solver, final Predicate<? super TcfaLoc> target) {
		checkNotNull(tcfa);
		checkNotNull(solver);
		checkNotNull(target);

		final TcfaLts lts = TcfaLts.create(tcfa);

		final ZonePrecision zonePrecision = ZonePrecision.create(Collections.emptySet());
		final ExplPrecision explPrecision = ExplPrecision.create(tcfa.getDataVars());
		final CompositePrecision<ZonePrecision, ExplPrecision> compositePrecision = CompositePrecision
				.create(zonePrecision, explPrecision);
		final LocPrecision<CompositePrecision<ZonePrecision, ExplPrecision>, TcfaLoc, TcfaEdge> locPrecision = LocPrecision
				.constant(compositePrecision);

		final Analysis<ZoneState, TcfaAction, ZonePrecision> zoneAnalysis = TcfaZoneAnalysis.getInstance();
		final Analysis<ExplState, ExprAction, ExplPrecision> explAnalysis = ExplAnalysis.create(solver, True());
		final Analysis<CompositeState<ZoneState, ExplState>, TcfaAction, CompositePrecision<ZonePrecision, ExplPrecision>> compositeAnalysis = CompositeAnalysis
				.create(zoneAnalysis, explAnalysis);
		final Analysis<LocState<CompositeState<ZoneState, ExplState>, TcfaLoc, TcfaEdge>, TcfaAction, LocPrecision<CompositePrecision<ZonePrecision, ExplPrecision>, TcfaLoc, TcfaEdge>> locAnalysis = LocAnalysis
				.create(tcfa.getInitLoc(), compositeAnalysis);

		final Analysis<LocState<CompositeState<ZoneState, ExplState>, TcfaLoc, TcfaEdge>, TcfaAction, NullPrecision> analysis = FixedPrecisionAnalysis
				.create(locAnalysis, locPrecision);

		final TcfaImpactRefiner refiner = TcfaImpactRefiner.create(tcfa);

		checker = ImpactChecker.create(lts, analysis, refiner, s -> target.test(s.getLoc()));
	}

	public static TcfaImpactChecker create(final TCFA tcfa, final Solver solver,
			final Predicate<? super TcfaLoc> target) {
		return new TcfaImpactChecker(tcfa, solver, target);
	}

	@Override
	public SafetyStatus<LocState<CompositeState<ZoneState, ExplState>, TcfaLoc, TcfaEdge>, TcfaAction> check(
			final NullPrecision precision) {
		checkNotNull(precision);
		return checker.check(precision);
	}

}
