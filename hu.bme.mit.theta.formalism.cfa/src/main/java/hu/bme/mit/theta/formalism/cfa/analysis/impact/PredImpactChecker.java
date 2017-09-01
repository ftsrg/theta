package hu.bme.mit.theta.formalism.cfa.analysis.impact;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static java.util.Collections.emptySet;

import java.util.function.Predicate;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.analysis.algorithm.ArgBuilder;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.impl.PrecMappingAnalysis;
import hu.bme.mit.theta.analysis.pred.PredAnalysis;
import hu.bme.mit.theta.analysis.pred.PredPrec;
import hu.bme.mit.theta.analysis.pred.PredState;
import hu.bme.mit.theta.analysis.pred.SimplePredPrec;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.formalism.cfa.CFA.Loc;
import hu.bme.mit.theta.formalism.cfa.analysis.CfaAction;
import hu.bme.mit.theta.formalism.cfa.analysis.CfaAnalysis;
import hu.bme.mit.theta.formalism.cfa.analysis.CfaPrec;
import hu.bme.mit.theta.formalism.cfa.analysis.CfaState;
import hu.bme.mit.theta.formalism.cfa.analysis.prec.ConstCfaPrec;
import hu.bme.mit.theta.solver.ItpSolver;

public final class PredImpactChecker implements SafetyChecker<CfaState<PredState>, CfaAction, UnitPrec> {

	private final ImpactChecker<CfaState<PredState>, CfaAction, UnitPrec> checker;

	private PredImpactChecker(final LTS<? super CfaState<PredState>, ? extends CfaAction> lts, final Loc initLoc,
			final Predicate<? super Loc> targetLocs, final ItpSolver solver) {
		checkNotNull(lts);
		checkNotNull(initLoc);
		checkNotNull(solver);

		final Analysis<PredState, ExprAction, PredPrec> predAnalysis = PredAnalysis.create(solver, True());

		final CfaPrec<PredPrec> fixedPrec = ConstCfaPrec.create(SimplePredPrec.create(emptySet(), solver));

		final Analysis<CfaState<PredState>, CfaAction, CfaPrec<PredPrec>> cfaAnalysis = CfaAnalysis.create(initLoc,
				predAnalysis);

		final Analysis<CfaState<PredState>, CfaAction, UnitPrec> analysis = PrecMappingAnalysis.create(cfaAnalysis,
				np -> fixedPrec);

		final Predicate<CfaState<?>> target = s -> targetLocs.test(s.getLoc());

		final ArgBuilder<CfaState<PredState>, CfaAction, UnitPrec> argBuilder = ArgBuilder.create(lts, analysis,
				target);

		final ImpactRefiner<CfaState<PredState>, CfaAction> refiner = PredImpactRefiner.create(solver);

		checker = ImpactChecker.create(argBuilder, refiner, s -> s.getLoc());
	}

	public static PredImpactChecker create(final LTS<? super CfaState<PredState>, ? extends CfaAction> lts,
			final Loc initLoc, final Predicate<? super Loc> targetLocs, final ItpSolver solver) {
		return new PredImpactChecker(lts, initLoc, targetLocs, solver);
	}

	@Override
	public SafetyResult<CfaState<PredState>, CfaAction> check(final UnitPrec prec) {
		return checker.check(prec);
	}

}
