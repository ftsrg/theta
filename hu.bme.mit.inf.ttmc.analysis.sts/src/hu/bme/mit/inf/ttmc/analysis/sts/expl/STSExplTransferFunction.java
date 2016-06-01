package hu.bme.mit.inf.ttmc.analysis.sts.expl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import hu.bme.mit.inf.ttmc.analysis.TransferFunction;
import hu.bme.mit.inf.ttmc.analysis.expl.ExplPrecision;
import hu.bme.mit.inf.ttmc.analysis.expl.ExplState;
import hu.bme.mit.inf.ttmc.analysis.sts.STSAction;
import hu.bme.mit.inf.ttmc.core.expr.impl.Exprs;
import hu.bme.mit.inf.ttmc.formalism.common.Valuation;
import hu.bme.mit.inf.ttmc.formalism.utils.PathUtils;
import hu.bme.mit.inf.ttmc.solver.Solver;

class STSExplTransferFunction implements TransferFunction<ExplState, ExplPrecision, STSAction> {

	private final Solver solver;

	STSExplTransferFunction(final Solver solver) {
		checkNotNull(solver);
		this.solver = solver;
	}

	@Override
	public Collection<ExplState> getSuccStates(final ExplState state, final ExplPrecision precision,
			final STSAction action) {
		checkNotNull(state);
		checkNotNull(precision);
		final Set<ExplState> succStates = new HashSet<>();
		solver.push();
		solver.add(PathUtils.unfold(state.toExpr(), 0));
		solver.add(PathUtils.unfold(action.getTrans(), 0));
		boolean moreSuccStates;
		do {
			moreSuccStates = solver.check().boolValue();
			if (moreSuccStates) {
				final Valuation nextSuccStateVal = PathUtils.extractValuation(solver.getModel(), 1);
				final ExplState nextSuccState = precision.mapToAbstractState(nextSuccStateVal);
				succStates.add(nextSuccState);
				solver.add(PathUtils.unfold(Exprs.Not(nextSuccState.toExpr()), 1));
			}
		} while (moreSuccStates);
		solver.pop();

		return succStates;
	}

}
