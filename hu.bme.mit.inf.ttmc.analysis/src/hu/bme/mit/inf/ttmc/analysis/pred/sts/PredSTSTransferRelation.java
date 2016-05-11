package hu.bme.mit.inf.ttmc.analysis.pred.sts;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import hu.bme.mit.inf.ttmc.analysis.TransferRelation;
import hu.bme.mit.inf.ttmc.analysis.pred.PredPrecision;
import hu.bme.mit.inf.ttmc.analysis.pred.PredState;
import hu.bme.mit.inf.ttmc.core.expr.impl.Exprs;
import hu.bme.mit.inf.ttmc.formalism.common.Valuation;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;
import hu.bme.mit.inf.ttmc.solver.Solver;

public class PredSTSTransferRelation implements TransferRelation<PredState, PredPrecision> {

	private final Solver solver;
	private final STS sts;

	public PredSTSTransferRelation(final STS sts, final Solver solver) {
		this.sts = checkNotNull(sts);
		this.solver = checkNotNull(solver);
	}

	@Override
	public Collection<? extends PredState> getSuccStates(final PredState state, final PredPrecision precision) {
		checkNotNull(state);
		checkNotNull(precision);
		final Set<PredState> succStates = new HashSet<>();
		solver.push();
		solver.add(sts.unroll(state.asExpr(), 0));
		solver.add(sts.unrollInv(0));
		solver.add(sts.unrollInv(1));
		solver.add(sts.unrollTrans(0));
		boolean moreSuccStates;
		do {
			moreSuccStates = solver.check().boolValue();
			if (moreSuccStates) {
				final Valuation nextSuccStateVal = sts.getConcreteState(solver.getModel(), 1);

				final PredState nextSuccState = PredState.create(nextSuccStateVal, precision);
				succStates.add(nextSuccState);
				solver.add(sts.unroll(Exprs.Not(nextSuccState.asExpr()), 1));
			}
		} while (moreSuccStates);
		solver.pop();

		return succStates;
	}

}
