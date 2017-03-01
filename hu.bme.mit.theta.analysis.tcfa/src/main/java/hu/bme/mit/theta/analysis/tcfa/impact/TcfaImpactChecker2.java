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
import hu.bme.mit.theta.analysis.impl.FixedPrecAnalysis;
import hu.bme.mit.theta.analysis.impl.NullPrec;
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
import hu.bme.mit.theta.analysis.tcfa.zone.itp.ItpZoneState;
import hu.bme.mit.theta.analysis.tcfa.zone.itp.TcfaItpZoneAnalysis;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.formalism.tcfa.TCFA;
import hu.bme.mit.theta.formalism.tcfa.TcfaEdge;
import hu.bme.mit.theta.formalism.tcfa.TcfaLoc;
import hu.bme.mit.theta.solver.Solver;

public final class TcfaImpactChecker2 implements
		SafetyChecker<LocState<Prod2State<ExplState, ItpZoneState>, TcfaLoc, TcfaEdge>, TcfaAction, NullPrec> {

	private final ImpactChecker<LocState<Prod2State<ExplState, ItpZoneState>, TcfaLoc, TcfaEdge>, TcfaAction, NullPrec> checker;

	private TcfaImpactChecker2(final TCFA tcfa, final Solver solver, final Predicate<? super TcfaLoc> targetLocs) {
		checkNotNull(tcfa);
		checkNotNull(solver);
		checkNotNull(targetLocs);

		final TcfaLts lts = TcfaLts.create(tcfa);

		final ExplPrec explPrec = ExplPrec.create(tcfa.getDataVars());
		final ZonePrec zonePrec = ZonePrec.create(tcfa.getClockVars());
		final Prod2Prec<ExplPrec, ZonePrec> prodPrec = ProdPrec.of(explPrec,
				zonePrec);
		final LocPrec<Prod2Prec<ExplPrec, ZonePrec>, TcfaLoc, TcfaEdge> locPrec = ConstLocPrec
				.create(prodPrec);

		final Analysis<ExplState, ExprAction, ExplPrec> explAnalysis = ExplAnalysis.create(solver, True());
		final Analysis<ItpZoneState, TcfaAction, ZonePrec> itpZoneAnalysis = TcfaItpZoneAnalysis.getInstance();
		final Analysis<Prod2State<ExplState, ItpZoneState>, TcfaAction, Prod2Prec<ExplPrec, ZonePrec>> compositeAnalysis = Prod2Analysis
				.create(explAnalysis, itpZoneAnalysis);
		final Analysis<LocState<Prod2State<ExplState, ItpZoneState>, TcfaLoc, TcfaEdge>, TcfaAction, LocPrec<Prod2Prec<ExplPrec, ZonePrec>, TcfaLoc, TcfaEdge>> locAnalysis = LocAnalysis
				.create(tcfa.getInitLoc(), compositeAnalysis);

		final Analysis<LocState<Prod2State<ExplState, ItpZoneState>, TcfaLoc, TcfaEdge>, TcfaAction, NullPrec> analysis = FixedPrecAnalysis
				.create(locAnalysis, locPrec);

		final Predicate<LocState<Prod2State<ExplState, ItpZoneState>, TcfaLoc, TcfaEdge>> target = s -> targetLocs
				.test(s.getLoc())
				|| (s.getState()._2().getState().isBottom() && !s.getState()._2().getInterpolant().isBottom());

		final ArgBuilder<LocState<Prod2State<ExplState, ItpZoneState>, TcfaLoc, TcfaEdge>, TcfaAction, NullPrec> argBuilder = ArgBuilder
				.create(lts, analysis, target);

		final TcfaImpactRefiner2 refiner = TcfaImpactRefiner2.create(tcfa);

		checker = ImpactChecker.create(argBuilder, refiner, s -> s.getLoc());
	}

	public static TcfaImpactChecker2 create(final TCFA tcfa, final Solver solver,
			final Predicate<? super TcfaLoc> target) {
		return new TcfaImpactChecker2(tcfa, solver, target);
	}

	@Override
	public SafetyResult<LocState<Prod2State<ExplState, ItpZoneState>, TcfaLoc, TcfaEdge>, TcfaAction> check(
			final NullPrec prec) {
		checkNotNull(prec);
		return checker.check(prec);
	}

}
