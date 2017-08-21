package hu.bme.mit.theta.analysis.expr.refinement;

import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.solver.ItpSolver;

public final class ExprTraceCombinedCheckers {

	public static ExprTraceChecker<ItpRefutation> createBwFwMinPrune(final Expr<BoolType> init,
			final Expr<BoolType> target, final ItpSolver solver) {
		final ExprTraceBwBinItpChecker bwChecker = ExprTraceBwBinItpChecker.create(init, target, solver);
		final ExprTraceFwBinItpChecker fwChecker = ExprTraceFwBinItpChecker.create(init, target, solver);
		final ExprTraceStatusMerger<ItpRefutation> merger = ExprTraceStatusMergers.minPruneIndex();
		return ExprTraceCombinedChecker.create(bwChecker, fwChecker, merger);
	}

	public static ExprTraceChecker<ItpRefutation> createBwFwMaxPrune(final Expr<BoolType> init,
			final Expr<BoolType> target, final ItpSolver solver) {
		final ExprTraceBwBinItpChecker bwChecker = ExprTraceBwBinItpChecker.create(init, target, solver);
		final ExprTraceFwBinItpChecker fwChecker = ExprTraceFwBinItpChecker.create(init, target, solver);
		final ExprTraceStatusMerger<ItpRefutation> merger = ExprTraceStatusMergers.maxPruneIndex();
		return ExprTraceCombinedChecker.create(bwChecker, fwChecker, merger);
	}
}
