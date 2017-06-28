package hu.bme.mit.theta.analysis.expl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import hu.bme.mit.theta.analysis.TransferFunction;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprStates;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.solver.Solver;

public final class ExplTransferFunction implements TransferFunction<ExplState, ExprAction, ExplPrec> {

	private final Solver solver;

	private ExplTransferFunction(final Solver solver) {
		this.solver = checkNotNull(solver);
	}

	public static ExplTransferFunction create(final Solver solver) {
		return new ExplTransferFunction(solver);
	}

	@Override
	public Collection<? extends ExplState> getSuccStates(final ExplState state, final ExprAction action,
			final ExplPrec prec) {
		checkNotNull(state);
		checkNotNull(action);
		checkNotNull(prec);
		return ExprStates.createStatesForExpr(solver, BoolExprs.And(state.toExpr(), action.toExpr()), 0,
				prec::createState, 1);
	}

}