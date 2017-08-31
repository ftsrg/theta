package hu.bme.mit.theta.analysis.cfa.impact;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;

import java.util.ArrayList;
import java.util.List;

import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.cfa.CfaAction;
import hu.bme.mit.theta.analysis.cfa.LocState;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.ExprTraceUtils;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceSeqItpChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceStatus;
import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation;
import hu.bme.mit.theta.analysis.pred.PredState;
import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.solver.ItpSolver;

public final class PredImpactRefiner implements ImpactRefiner<LocState<PredState>, CfaAction> {

	private final ExprTraceSeqItpChecker traceChecker;

	private PredImpactRefiner(final ItpSolver solver) {
		checkNotNull(solver);
		traceChecker = ExprTraceSeqItpChecker.create(True(), True(), solver);
	}

	public static PredImpactRefiner create(final ItpSolver solver) {
		return new PredImpactRefiner(solver);
	}

	@Override
	public RefinementResult<LocState<PredState>, CfaAction> refine(final Trace<LocState<PredState>, CfaAction> cex) {
		final List<CfaAction> actions = cex.getActions();

		final Trace<ExprState, ExprAction> exprTrace = ExprTraceUtils.traceFrom(actions);
		final ExprTraceStatus<ItpRefutation> traceStatus = traceChecker.check(exprTrace);

		if (traceStatus.isFeasible()) {
			return RefinementResult.unsuccesful();

		} else if (traceStatus.isInfeasible()) {
			final ItpRefutation refuation = traceStatus.asInfeasible().getRefutation();
			final List<Expr<BoolType>> exprs = refuation.toList();

			final List<LocState<PredState>> refinedStates = new ArrayList<>();
			for (int i = 0; i < exprs.size(); i++) {
				final List<Expr<BoolType>> newPreds = new ArrayList<>();

				final LocState<PredState> state = cex.getState(i);
				final Expr<BoolType> expr = exprs.get(i);

				newPreds.addAll(state.getState().getPreds());
				newPreds.add(expr);

				final LocState<PredState> refinedState = state.withState(PredState.of(newPreds));

				refinedStates.add(refinedState);
			}

			final Trace<LocState<PredState>, CfaAction> trace = Trace.of(refinedStates, actions);
			return RefinementResult.succesful(trace);
		} else {
			throw new AssertionError();
		}
	}

}
