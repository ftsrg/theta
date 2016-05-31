package hu.bme.mit.inf.ttmc.analysis.expl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import hu.bme.mit.inf.ttmc.analysis.TransferFunction;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.expr.impl.Exprs;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.common.Valuation;
import hu.bme.mit.inf.ttmc.formalism.utils.PathUtils;
import hu.bme.mit.inf.ttmc.solver.Solver;

class ExplTransferFunction implements TransferFunction<ExplState, ExplPrecision> {

	private final Solver solver;
	private final Expr<? extends BoolType> trans;

	ExplTransferFunction(final Solver solver, final Expr<? extends BoolType> trans) {
		checkNotNull(solver);
		checkNotNull(trans);
		this.solver = solver;
		this.trans = trans;
	}

	@Override
	public Collection<ExplState> getSuccStates(final ExplState state, final ExplPrecision precision) {
		checkNotNull(state);
		checkNotNull(precision);
		final Set<ExplState> succStates = new HashSet<>();
		solver.push();
		solver.add(PathUtils.unfold(state.toExpr(), 0));
		solver.add(PathUtils.unfold(trans, 0));
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
