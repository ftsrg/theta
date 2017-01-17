package hu.bme.mit.theta.analysis.tcfa.impact;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.expr.impl.Exprs.True;

import java.util.function.Predicate;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.algorithm.ArgBuilder;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyStatus;
import hu.bme.mit.theta.analysis.algorithm.impact.ImpactChecker;
import hu.bme.mit.theta.analysis.expl.ExplAnalysis;
import hu.bme.mit.theta.analysis.expl.ExplPrecision;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.impl.FixedPrecisionAnalysis;
import hu.bme.mit.theta.analysis.impl.NullPrecision;
import hu.bme.mit.theta.analysis.loc.LocAnalysis;
import hu.bme.mit.theta.analysis.loc.LocPrecision;
import hu.bme.mit.theta.analysis.loc.LocState;
import hu.bme.mit.theta.analysis.prod.Prod2Analysis;
import hu.bme.mit.theta.analysis.prod.Prod2Precision;
import hu.bme.mit.theta.analysis.prod.Prod2State;
import hu.bme.mit.theta.analysis.prod.ProdPrecision;
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
		SafetyChecker<LocState<Prod2State<ExplState, ZoneState>, TcfaLoc, TcfaEdge>, TcfaAction, NullPrecision> {

	private final ImpactChecker<LocState<Prod2State<ExplState, ZoneState>, TcfaLoc, TcfaEdge>, TcfaAction, NullPrecision> checker;

	private TcfaImpactChecker(final TCFA tcfa, final Solver solver, final Predicate<? super TcfaLoc> targetLocs) {
		checkNotNull(tcfa);
		checkNotNull(solver);
		checkNotNull(targetLocs);

		final TcfaLts lts = TcfaLts.create(tcfa);

		final ExplPrecision explPrecision = ExplPrecision.create(tcfa.getDataVars());
		final ZonePrecision zonePrecision = ZonePrecision.create(tcfa.getClockVars());
		final Prod2Precision<ExplPrecision, ZonePrecision> prodPrecision = ProdPrecision.of(explPrecision,
				zonePrecision);
		final LocPrecision<Prod2Precision<ExplPrecision, ZonePrecision>, TcfaLoc, TcfaEdge> locPrecision = LocPrecision
				.constant(prodPrecision);

		final Analysis<ExplState, ExprAction, ExplPrecision> explAnalysis = ExplAnalysis.create(solver, True());
		final Analysis<ZoneState, TcfaAction, ZonePrecision> zoneAnalysis = TcfaZoneAnalysis.getInstance();
		final Analysis<Prod2State<ExplState, ZoneState>, TcfaAction, Prod2Precision<ExplPrecision, ZonePrecision>> compositeAnalysis = Prod2Analysis
				.create(explAnalysis, zoneAnalysis);
		final Analysis<LocState<Prod2State<ExplState, ZoneState>, TcfaLoc, TcfaEdge>, TcfaAction, LocPrecision<Prod2Precision<ExplPrecision, ZonePrecision>, TcfaLoc, TcfaEdge>> locAnalysis = LocAnalysis
				.create(tcfa.getInitLoc(), compositeAnalysis);

		final Analysis<LocState<Prod2State<ExplState, ZoneState>, TcfaLoc, TcfaEdge>, TcfaAction, NullPrecision> analysis = FixedPrecisionAnalysis
				.create(locAnalysis, locPrecision);

		final Predicate<LocState<?, TcfaLoc, ?>> target = s -> targetLocs.test(s.getLoc());

		final ArgBuilder<LocState<Prod2State<ExplState, ZoneState>, TcfaLoc, TcfaEdge>, TcfaAction, NullPrecision> argBuilder = ArgBuilder
				.create(lts, analysis, target);

		final TcfaImpactRefiner refiner = TcfaImpactRefiner.create(tcfa);

		checker = ImpactChecker.create(argBuilder, refiner, s -> s.getLoc());
	}

	public static TcfaImpactChecker create(final TCFA tcfa, final Solver solver,
			final Predicate<? super TcfaLoc> target) {
		return new TcfaImpactChecker(tcfa, solver, target);
	}

	@Override
	public SafetyStatus<LocState<Prod2State<ExplState, ZoneState>, TcfaLoc, TcfaEdge>, TcfaAction> check(
			final NullPrecision precision) {
		checkNotNull(precision);
		return checker.check(precision);
	}

}
