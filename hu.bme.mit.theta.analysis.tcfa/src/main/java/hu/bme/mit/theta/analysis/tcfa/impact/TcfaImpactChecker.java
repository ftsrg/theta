package hu.bme.mit.theta.analysis.tcfa.impact;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.expr.impl.Exprs.True;

import java.util.function.Predicate;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.algorithm.ArgBuilder;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.impact.ImpactChecker;
import hu.bme.mit.theta.analysis.expl.ExplAnalysis;
import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.impl.NullPrec;
import hu.bme.mit.theta.analysis.impl.PrecMappingAnalysis;
import hu.bme.mit.theta.analysis.loc.ConstLocPrec;
import hu.bme.mit.theta.analysis.loc.LocAnalysis;
import hu.bme.mit.theta.analysis.loc.LocPrec;
import hu.bme.mit.theta.analysis.loc.LocState;
import hu.bme.mit.theta.analysis.prod.Prod2Analysis;
import hu.bme.mit.theta.analysis.prod.Prod2Prec;
import hu.bme.mit.theta.analysis.prod.Prod2State;
import hu.bme.mit.theta.analysis.prod.ProdPrec;
import hu.bme.mit.theta.analysis.tcfa.TcfaAction;
import hu.bme.mit.theta.analysis.tcfa.TcfaLts;
import hu.bme.mit.theta.analysis.tcfa.zone.TcfaZoneAnalysis;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;
import hu.bme.mit.theta.formalism.tcfa.TCFA;
import hu.bme.mit.theta.formalism.tcfa.TcfaEdge;
import hu.bme.mit.theta.formalism.tcfa.TcfaLoc;
import hu.bme.mit.theta.solver.Solver;

public final class TcfaImpactChecker
		implements SafetyChecker<LocState<Prod2State<ExplState, ZoneState>, TcfaLoc, TcfaEdge>, TcfaAction, NullPrec> {

	private final ImpactChecker<LocState<Prod2State<ExplState, ZoneState>, TcfaLoc, TcfaEdge>, TcfaAction, NullPrec> checker;

	private TcfaImpactChecker(final TCFA tcfa, final Solver solver, final Predicate<? super TcfaLoc> targetLocs) {
		checkNotNull(tcfa);
		checkNotNull(solver);
		checkNotNull(targetLocs);

		final TcfaLts lts = TcfaLts.create(tcfa);

		final ExplPrec explPrec = ExplPrec.create(tcfa.getDataVars());
		final ZonePrec zonePrec = ZonePrec.create(tcfa.getClockVars());
		final Prod2Prec<ExplPrec, ZonePrec> prodPrec = ProdPrec.of(explPrec, zonePrec);
		final LocPrec<Prod2Prec<ExplPrec, ZonePrec>, TcfaLoc, TcfaEdge> locPrec = ConstLocPrec.create(prodPrec);

		final Analysis<ExplState, ExprAction, ExplPrec> explAnalysis = ExplAnalysis.create(solver, True());
		final Analysis<ZoneState, TcfaAction, ZonePrec> zoneAnalysis = TcfaZoneAnalysis.getInstance();
		final Analysis<Prod2State<ExplState, ZoneState>, TcfaAction, Prod2Prec<ExplPrec, ZonePrec>> compositeAnalysis = Prod2Analysis
				.create(explAnalysis, zoneAnalysis);
		final Analysis<LocState<Prod2State<ExplState, ZoneState>, TcfaLoc, TcfaEdge>, TcfaAction, LocPrec<Prod2Prec<ExplPrec, ZonePrec>, TcfaLoc, TcfaEdge>> locAnalysis = LocAnalysis
				.create(tcfa.getInitLoc(), compositeAnalysis);

		final Analysis<LocState<Prod2State<ExplState, ZoneState>, TcfaLoc, TcfaEdge>, TcfaAction, NullPrec> analysis = PrecMappingAnalysis
				.create(locAnalysis, np -> locPrec);

		final Predicate<LocState<?, TcfaLoc, ?>> target = s -> targetLocs.test(s.getLoc());

		final ArgBuilder<LocState<Prod2State<ExplState, ZoneState>, TcfaLoc, TcfaEdge>, TcfaAction, NullPrec> argBuilder = ArgBuilder
				.create(lts, analysis, target);

		final TcfaImpactRefiner refiner = TcfaImpactRefiner.create(tcfa);

		checker = ImpactChecker.create(argBuilder, refiner, s -> s.getLoc());
	}

	public static TcfaImpactChecker create(final TCFA tcfa, final Solver solver,
			final Predicate<? super TcfaLoc> target) {
		return new TcfaImpactChecker(tcfa, solver, target);
	}

	@Override
	public SafetyResult<LocState<Prod2State<ExplState, ZoneState>, TcfaLoc, TcfaEdge>, TcfaAction> check(
			final NullPrec prec) {
		checkNotNull(prec);
		return checker.check(prec);
	}

}
