package hu.bme.mit.theta.analysis.sts.expl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.HashSet;

import hu.bme.mit.theta.analysis.TransferFunction;
import hu.bme.mit.theta.analysis.expl.ExplPrecision;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.sts.StsAction;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.impl.Exprs;
import hu.bme.mit.theta.core.model.impl.Valuation;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.utils.impl.PathUtils;
import hu.bme.mit.theta.formalism.sts.STS;
import hu.bme.mit.theta.solver.Solver;

class StsExplTransferFunction implements TransferFunction<ExplState, StsAction, ExplPrecision> {

	private final Collection<Expr<? extends BoolType>> invar;
	private final Solver solver;

	StsExplTransferFunction(final STS sts, final Solver solver) {
		this.invar = checkNotNull(sts.getInvar());
		this.solver = checkNotNull(solver);
	}

	@Override
	public Collection<ExplState> getSuccStates(final ExplState state, final StsAction action,
			final ExplPrecision precision) {
		checkNotNull(state);
		checkNotNull(action);
		checkNotNull(precision);

		final Collection<ExplState> succStates = new HashSet<>();

		solver.push();
		solver.add(PathUtils.unfold(state.toExpr(), 0));
		action.getTrans().stream().forEach(t -> solver.add(PathUtils.unfold(t, 0)));
		// TODO: optimization: cache the unfolded invar for 0 and 1
		invar.stream().forEach(i -> solver.add(PathUtils.unfold(i, 0)));
		invar.stream().forEach(i -> solver.add(PathUtils.unfold(i, 1)));
		boolean moreSuccStates;
		do {
			moreSuccStates = solver.check().isSat();
			if (moreSuccStates) {
				final Valuation nextSuccStateVal = PathUtils.extractValuation(solver.getModel(), 1);
				final ExplState nextSuccState = precision.createState(nextSuccStateVal);
				succStates.add(nextSuccState);
				solver.add(PathUtils.unfold(Exprs.Not(nextSuccState.toExpr()), 1));
			}
		} while (moreSuccStates);
		solver.pop();

		return succStates;
	}

}
