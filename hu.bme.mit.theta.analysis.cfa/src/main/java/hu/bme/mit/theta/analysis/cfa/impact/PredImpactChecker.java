package hu.bme.mit.theta.analysis.cfa.impact;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static java.util.Collections.emptySet;

import java.util.function.Predicate;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.analysis.algorithm.ArgBuilder;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.cfa.CfaAction;
import hu.bme.mit.theta.analysis.cfa.ConstLocPrec;
import hu.bme.mit.theta.analysis.cfa.LocAnalysis;
import hu.bme.mit.theta.analysis.cfa.LocPrec;
import hu.bme.mit.theta.analysis.cfa.LocState;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.impl.PrecMappingAnalysis;
import hu.bme.mit.theta.analysis.pred.PredAnalysis;
import hu.bme.mit.theta.analysis.pred.PredPrec;
import hu.bme.mit.theta.analysis.pred.PredState;
import hu.bme.mit.theta.analysis.pred.SimplePredPrec;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.formalism.cfa.CFA.Loc;
import hu.bme.mit.theta.solver.ItpSolver;

public final class PredImpactChecker implements SafetyChecker<LocState<PredState>, CfaAction, UnitPrec> {

	private final ImpactChecker<LocState<PredState>, CfaAction, UnitPrec> checker;

	private PredImpactChecker(final LTS<? super LocState<PredState>, ? extends CfaAction> lts, final Loc initLoc,
			final Predicate<? super Loc> targetLocs, final ItpSolver solver) {
		checkNotNull(lts);
		checkNotNull(initLoc);
		checkNotNull(solver);

		final Analysis<PredState, ExprAction, PredPrec> predAnalysis = PredAnalysis.create(solver, True());

		final LocPrec<PredPrec> fixedPrec = ConstLocPrec.create(SimplePredPrec.create(emptySet(), solver));

		final Analysis<LocState<PredState>, CfaAction, LocPrec<PredPrec>> cfaAnalysis = LocAnalysis.create(initLoc,
				predAnalysis);

		final Analysis<LocState<PredState>, CfaAction, UnitPrec> analysis = PrecMappingAnalysis.create(cfaAnalysis,
				np -> fixedPrec);

		final Predicate<LocState<?>> target = s -> targetLocs.test(s.getLoc());

		final ArgBuilder<LocState<PredState>, CfaAction, UnitPrec> argBuilder = ArgBuilder.create(lts, analysis,
				target);

		final ImpactRefiner<LocState<PredState>, CfaAction> refiner = PredImpactRefiner.create(solver);

		checker = ImpactChecker.create(argBuilder, refiner, s -> s.getLoc());
	}

	public static PredImpactChecker create(final LTS<? super LocState<PredState>, ? extends CfaAction> lts,
			final Loc initLoc, final Predicate<? super Loc> targetLocs, final ItpSolver solver) {
		return new PredImpactChecker(lts, initLoc, targetLocs, solver);
	}

	@Override
	public SafetyResult<LocState<PredState>, CfaAction> check(final UnitPrec prec) {
		return checker.check(prec);
	}

}
