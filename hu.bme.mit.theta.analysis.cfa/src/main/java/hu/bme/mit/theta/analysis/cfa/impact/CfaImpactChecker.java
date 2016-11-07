package hu.bme.mit.theta.analysis.cfa.impact;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.expr.impl.Exprs.True;
import static java.util.Collections.emptySet;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyStatus;
import hu.bme.mit.theta.analysis.algorithm.impact.ImpactChecker;
import hu.bme.mit.theta.analysis.algorithm.impact.ImpactRefiner;
import hu.bme.mit.theta.analysis.cfa.CfaAction;
import hu.bme.mit.theta.analysis.cfa.CfaAnalysis;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.impl.FixedPrecisionAnalysis;
import hu.bme.mit.theta.analysis.impl.NullActionFunction;
import hu.bme.mit.theta.analysis.impl.NullPrecision;
import hu.bme.mit.theta.analysis.loc.LocPrecision;
import hu.bme.mit.theta.analysis.loc.LocState;
import hu.bme.mit.theta.analysis.pred.PredAnalysis;
import hu.bme.mit.theta.analysis.pred.PredPrecision;
import hu.bme.mit.theta.analysis.pred.PredState;
import hu.bme.mit.theta.analysis.pred.SimplePredPrecision;
import hu.bme.mit.theta.formalism.cfa.CFA;
import hu.bme.mit.theta.formalism.cfa.CfaEdge;
import hu.bme.mit.theta.formalism.cfa.CfaLoc;
import hu.bme.mit.theta.solver.ItpSolver;

public final class CfaImpactChecker
		implements SafetyChecker<LocState<PredState, CfaLoc, CfaEdge>, CfaAction, NullPrecision> {

	private final ImpactChecker<LocState<PredState, CfaLoc, CfaEdge>, CfaAction, NullPrecision> checker;

	private CfaImpactChecker(final CFA cfa, final ItpSolver solver) {
		checkNotNull(cfa);

		final Analysis<PredState, ExprAction, PredPrecision> predAnalysis = PredAnalysis.create(solver, True(),
				NullActionFunction.getInstance());

		final LocPrecision<PredPrecision, CfaLoc, CfaEdge> fixedPrecision = LocPrecision
				.constant(SimplePredPrecision.create(emptySet(), solver));

		final Analysis<LocState<PredState, CfaLoc, CfaEdge>, CfaAction, LocPrecision<PredPrecision, CfaLoc, CfaEdge>> cfaAnalysis = CfaAnalysis
				.create(cfa.getInitLoc(), predAnalysis);

		final Analysis<LocState<PredState, CfaLoc, CfaEdge>, CfaAction, NullPrecision> analysis = FixedPrecisionAnalysis
				.create(cfaAnalysis, fixedPrecision);

		final ImpactRefiner<LocState<PredState, CfaLoc, CfaEdge>, CfaAction> refiner = CfaImpactRefiner.create(solver);

		checker = ImpactChecker.create(analysis, refiner, s -> s.getLoc().equals(cfa.getErrorLoc()));
	}

	public static CfaImpactChecker create(final CFA cfa, final ItpSolver solver) {
		return new CfaImpactChecker(cfa, solver);
	}

	@Override
	public SafetyStatus<LocState<PredState, CfaLoc, CfaEdge>, CfaAction> check(final NullPrecision precision) {
		return checker.check(precision);
	}

}
