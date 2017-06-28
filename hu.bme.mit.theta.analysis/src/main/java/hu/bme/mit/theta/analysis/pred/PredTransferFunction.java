package hu.bme.mit.theta.analysis.pred;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import hu.bme.mit.theta.analysis.TransferFunction;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprStates;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.solver.Solver;

public final class PredTransferFunction implements TransferFunction<PredState, ExprAction, PredPrec> {

	private final Solver solver;

	private PredTransferFunction(final Solver solver) {
		this.solver = checkNotNull(solver);
	}

	public static PredTransferFunction create(final Solver solver) {
		return new PredTransferFunction(solver);
	}

	@Override
	public Collection<? extends PredState> getSuccStates(final PredState state, final ExprAction action,
			final PredPrec prec) {
		checkNotNull(state);
		checkNotNull(action);
		checkNotNull(prec);

		return ExprStates.createStatesForExpr(solver, BoolExprs.And(state.toExpr(), action.toExpr()), 0,
				prec::createState, 1);
	}

}
