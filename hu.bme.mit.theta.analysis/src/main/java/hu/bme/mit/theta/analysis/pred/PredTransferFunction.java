package hu.bme.mit.theta.analysis.pred;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import hu.bme.mit.theta.analysis.TransferFunction;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.core.expr.impl.Exprs;
import hu.bme.mit.theta.core.model.impl.Valuation;
import hu.bme.mit.theta.core.utils.impl.PathUtils;
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

		final Set<PredState> succStates = new HashSet<>();
		solver.push();
		solver.add(PathUtils.unfold(state.toExpr(), 0));
		solver.add(PathUtils.unfold(action.toExpr(), 0));

		boolean moreSuccStates;
		do {
			moreSuccStates = solver.check().isSat();
			if (moreSuccStates) {
				final Valuation nextSuccStateVal = PathUtils.extractValuation(solver.getModel(), action.nextIndexing());

				final PredState nextSuccState = prec.createState(nextSuccStateVal);
				succStates.add(nextSuccState);
				solver.add(PathUtils.unfold(Exprs.Not(nextSuccState.toExpr()), action.nextIndexing()));
			}
		} while (moreSuccStates);
		solver.pop();

		return succStates;
	}

}
