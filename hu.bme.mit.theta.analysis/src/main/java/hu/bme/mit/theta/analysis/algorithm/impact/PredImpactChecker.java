package hu.bme.mit.theta.analysis.algorithm.impact;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.expr.impl.Exprs.True;
import static java.util.Collections.emptySet;

import java.util.function.Predicate;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.analysis.algorithm.ArgBuilder;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyStatus;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.impl.FixedPrecisionAnalysis;
import hu.bme.mit.theta.analysis.impl.NullPrecision;
import hu.bme.mit.theta.analysis.loc.ConstLocPrecision;
import hu.bme.mit.theta.analysis.loc.LocAction;
import hu.bme.mit.theta.analysis.loc.LocAnalysis;
import hu.bme.mit.theta.analysis.loc.LocPrecision;
import hu.bme.mit.theta.analysis.loc.LocState;
import hu.bme.mit.theta.analysis.pred.PredAnalysis;
import hu.bme.mit.theta.analysis.pred.PredPrecision;
import hu.bme.mit.theta.analysis.pred.PredState;
import hu.bme.mit.theta.analysis.pred.SimplePredPrecision;
import hu.bme.mit.theta.formalism.common.Edge;
import hu.bme.mit.theta.formalism.common.Loc;
import hu.bme.mit.theta.solver.ItpSolver;

public final class PredImpactChecker<L extends Loc<L, E>, E extends Edge<L, E>>
		implements SafetyChecker<LocState<PredState, L, E>, LocAction<L, E>, NullPrecision> {

	private final ImpactChecker<LocState<PredState, L, E>, LocAction<L, E>, NullPrecision> checker;

	private PredImpactChecker(final LTS<? super LocState<PredState, L, E>, ? extends LocAction<L, E>> lts,
			final L initLoc, final Predicate<? super L> targetLocs, final ItpSolver solver) {
		checkNotNull(lts);
		checkNotNull(initLoc);
		checkNotNull(solver);

		final Analysis<PredState, ExprAction, PredPrecision> predAnalysis = PredAnalysis.create(solver, True());

		final LocPrecision<PredPrecision, L, E> fixedPrecision = ConstLocPrecision
				.create(SimplePredPrecision.create(emptySet(), solver));

		final Analysis<LocState<PredState, L, E>, LocAction<L, E>, LocPrecision<PredPrecision, L, E>> cfaAnalysis = LocAnalysis
				.create(initLoc, predAnalysis);

		final Analysis<LocState<PredState, L, E>, LocAction<L, E>, NullPrecision> analysis = FixedPrecisionAnalysis
				.create(cfaAnalysis, fixedPrecision);

		final Predicate<LocState<?, L, ?>> target = s -> targetLocs.test(s.getLoc());

		final ArgBuilder<LocState<PredState, L, E>, LocAction<L, E>, NullPrecision> argBuilder = ArgBuilder.create(lts,
				analysis, target);

		final ImpactRefiner<LocState<PredState, L, E>, LocAction<L, E>> refiner = PredImpactRefiner.create(solver);

		checker = ImpactChecker.create(argBuilder, refiner, s -> s.getLoc());
	}

	public static <L extends Loc<L, E>, E extends Edge<L, E>> PredImpactChecker<L, E> create(
			final LTS<? super LocState<PredState, L, E>, ? extends LocAction<L, E>> lts, final L initLoc,
			final Predicate<? super L> targetLocs, final ItpSolver solver) {
		return new PredImpactChecker<>(lts, initLoc, targetLocs, solver);
	}

	@Override
	public SafetyStatus<LocState<PredState, L, E>, LocAction<L, E>> check(final NullPrecision precision) {
		return checker.check(precision);
	}

}
