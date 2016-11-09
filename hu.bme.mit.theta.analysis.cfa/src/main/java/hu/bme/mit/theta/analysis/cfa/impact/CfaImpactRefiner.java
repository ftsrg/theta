package hu.bme.mit.theta.analysis.cfa.impact;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.List;

import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.impact.ImpactRefiner;
import hu.bme.mit.theta.analysis.cfa.CfaAction;
import hu.bme.mit.theta.analysis.expr.ExprTrace;
import hu.bme.mit.theta.analysis.expr.ExprTraceStatus;
import hu.bme.mit.theta.analysis.loc.LocState;
import hu.bme.mit.theta.analysis.pred.PredState;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.formalism.cfa.CfaEdge;
import hu.bme.mit.theta.formalism.cfa.CfaLoc;
import hu.bme.mit.theta.solver.ItpSolver;

public final class CfaImpactRefiner implements ImpactRefiner<LocState<PredState, CfaLoc, CfaEdge>, CfaAction> {

	final ItpSolver solver;

	private CfaImpactRefiner(final ItpSolver solver) {
		this.solver = checkNotNull(solver);
	}

	public static CfaImpactRefiner create(final ItpSolver solver) {
		return new CfaImpactRefiner(solver);
	}

	@Override
	public RefinementResult<LocState<PredState, CfaLoc, CfaEdge>, CfaAction> refine(
			final Trace<LocState<PredState, CfaLoc, CfaEdge>, CfaAction> cex) {
		final List<CfaAction> actions = cex.getActions();

		final ExprTrace exprTrace = ExprTrace.of(actions);
		final ExprTraceStatus traceStatus = exprTrace.check(solver);

		if (traceStatus.isFeasable()) {
			return RefinementResult.unsuccesful();

		} else if (traceStatus.isUnfeasable()) {
			final List<Expr<? extends BoolType>> exprs = traceStatus.asUnfeasable().getExprs();

			final List<LocState<PredState, CfaLoc, CfaEdge>> refinedStates = new ArrayList<>();
			for (int i = 0; i < exprs.size(); i++) {
				final List<Expr<? extends BoolType>> newPreds = new ArrayList<>();

				final LocState<PredState, CfaLoc, CfaEdge> state = cex.getState(i);
				final Expr<? extends BoolType> expr = exprs.get(i);

				newPreds.addAll(state.getState().getPreds());
				newPreds.add(expr);

				final LocState<PredState, CfaLoc, CfaEdge> refinedState = state.withState(
						PredState.create(newPreds));

				refinedStates.add(refinedState);
			}

			final Trace<LocState<PredState, CfaLoc, CfaEdge>, CfaAction> trace = Trace.of(refinedStates, actions);
			return RefinementResult.succesful(trace);
		} else {
			throw new AssertionError();
		}
	}

}
