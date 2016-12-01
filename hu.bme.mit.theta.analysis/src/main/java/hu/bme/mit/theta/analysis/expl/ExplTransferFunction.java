package hu.bme.mit.theta.analysis.expl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.HashSet;

import hu.bme.mit.theta.analysis.TransferFunction;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.core.expr.impl.Exprs;
import hu.bme.mit.theta.core.model.impl.Valuation;
import hu.bme.mit.theta.core.utils.impl.PathUtils;
import hu.bme.mit.theta.solver.Solver;

public final class ExplTransferFunction implements TransferFunction<ExplState, ExprAction, ExplPrecision> {

	private final Solver solver;

	private ExplTransferFunction(final Solver solver) {
		this.solver = checkNotNull(solver);
	}

	public static ExplTransferFunction create(final Solver solver) {
		return new ExplTransferFunction(solver);
	}

	@Override
	public Collection<? extends ExplState> getSuccStates(final ExplState state, final ExprAction action,
			final ExplPrecision precision) {
		checkNotNull(state);
		checkNotNull(action);
		checkNotNull(precision);

		final Collection<ExplState> succStates = new HashSet<>();

		solver.push();
		solver.add(PathUtils.unfold(state.toExpr(), 0));
		solver.add(PathUtils.unfold(action.toExpr(), 0));

		boolean moreSuccStates;
		do {
			moreSuccStates = solver.check().isSat();
			if (moreSuccStates) {
				final Valuation nextSuccStateVal = PathUtils.extractValuation(solver.getModel(), action.nextIndexing());
				final ExplState nextSuccState = precision.createState(nextSuccStateVal);
				succStates.add(nextSuccState);
				solver.add(PathUtils.unfold(Exprs.Not(nextSuccState.toExpr()), action.nextIndexing()));
			}
		} while (moreSuccStates);
		solver.pop();

		return succStates;
	}

}