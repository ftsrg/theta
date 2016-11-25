package hu.bme.mit.theta.analysis.algorithm.impact;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.List;

import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.expr.ExprTrace;
import hu.bme.mit.theta.analysis.expr.ExprTraceStatus;
import hu.bme.mit.theta.analysis.loc.LocAction;
import hu.bme.mit.theta.analysis.loc.LocState;
import hu.bme.mit.theta.analysis.pred.PredState;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.formalism.common.Edge;
import hu.bme.mit.theta.formalism.common.Loc;
import hu.bme.mit.theta.solver.ItpSolver;

public final class PredImpactRefiner<L extends Loc<L, E>, E extends Edge<L, E>>
		implements ImpactRefiner<LocState<PredState, L, E>, LocAction<L, E>> {

	final ItpSolver solver;

	private PredImpactRefiner(final ItpSolver solver) {
		this.solver = checkNotNull(solver);
	}

	public static <L extends Loc<L, E>, E extends Edge<L, E>> PredImpactRefiner<L, E> create(final ItpSolver solver) {
		return new PredImpactRefiner<>(solver);
	}

	@Override
	public RefinementResult<LocState<PredState, L, E>, LocAction<L, E>> refine(
			final Trace<LocState<PredState, L, E>, LocAction<L, E>> cex) {
		final List<LocAction<L, E>> actions = cex.getActions();

		final ExprTrace exprTrace = ExprTrace.of(actions);
		final ExprTraceStatus traceStatus = exprTrace.check(solver);

		if (traceStatus.isFeasable()) {
			return RefinementResult.unsuccesful();

		} else if (traceStatus.isUnfeasable()) {
			final List<Expr<? extends BoolType>> exprs = traceStatus.asUnfeasable().getExprs();

			final List<LocState<PredState, L, E>> refinedStates = new ArrayList<>();
			for (int i = 0; i < exprs.size(); i++) {
				final List<Expr<? extends BoolType>> newPreds = new ArrayList<>();

				final LocState<PredState, L, E> state = cex.getState(i);
				final Expr<? extends BoolType> expr = exprs.get(i);

				newPreds.addAll(state.getState().getPreds());
				newPreds.add(expr);

				final LocState<PredState, L, E> refinedState = state.withState(PredState.of(newPreds));

				refinedStates.add(refinedState);
			}

			final Trace<LocState<PredState, L, E>, LocAction<L, E>> trace = Trace.of(refinedStates, actions);
			return RefinementResult.succesful(trace);
		} else {
			throw new AssertionError();
		}
	}

}
