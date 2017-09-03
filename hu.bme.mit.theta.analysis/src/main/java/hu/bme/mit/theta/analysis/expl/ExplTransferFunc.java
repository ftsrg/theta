package hu.bme.mit.theta.analysis.expl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import hu.bme.mit.theta.analysis.TransferFunc;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprStates;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.solver.Solver;

public final class ExplTransferFunc implements TransferFunc<ExplState, ExprAction, ExplPrec> {

	private final Solver solver;

	private ExplTransferFunc(final Solver solver) {
		this.solver = checkNotNull(solver);
	}

	public static ExplTransferFunc create(final Solver solver) {
		return new ExplTransferFunc(solver);
	}

	@Override
	public Collection<? extends ExplState> getSuccStates(final ExplState state, final ExprAction action,
			final ExplPrec prec) {
		checkNotNull(state);
		checkNotNull(action);
		checkNotNull(prec);
		return ExprStates.createStatesForExpr(solver, BoolExprs.And(state.toExpr(), action.toExpr()), 0,
				prec::createState, action.nextIndexing());
	}

}