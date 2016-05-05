package hu.bme.mit.inf.ttmc.analysis.expl.sts;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import hu.bme.mit.inf.ttmc.analysis.ExprState;
import hu.bme.mit.inf.ttmc.analysis.TransferRelation;
import hu.bme.mit.inf.ttmc.analysis.expl.ExplPrecision;
import hu.bme.mit.inf.ttmc.analysis.expl.ExplState;
import hu.bme.mit.inf.ttmc.core.expr.impl.Exprs;
import hu.bme.mit.inf.ttmc.formalism.common.Valuation;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;
import hu.bme.mit.inf.ttmc.solver.Solver;

public class ExplSTSTransferRelation implements TransferRelation<ExplState, ExplPrecision> {

	private final Solver solver;
	private final STS sts;

	public ExplSTSTransferRelation(final STS sts, final Solver solver) {
		this.sts = checkNotNull(sts);
		this.solver = checkNotNull(solver);
	}

	@Override
	public Collection<? extends ExplState> getSuccStates(final ExplState state, final ExplPrecision precision) {
		checkNotNull(state);
		final Set<ExplState> succStates = new HashSet<>();
		boolean moreSuccessors;
		do {
			Valuation nextSuccVal = null;
			solver.push();
			solver.add(sts.unroll(state.asExpr(), 0));
			solver.add(sts.unrollInv(0));
			solver.add(sts.unrollInv(1));
			solver.add(sts.unrollTrans(0));
			for (final ExprState existingSucc : succStates)
				solver.add(sts.unroll(Exprs.Not(existingSucc.asExpr()), 1));

			moreSuccessors = solver.check().boolValue();
			if (moreSuccessors) {
				nextSuccVal = sts.getConcreteState(solver.getModel(), 1, precision.getVisibleVars());
				succStates.add(ExplState.create(nextSuccVal));
			}

			solver.pop();

		} while (moreSuccessors);

		return succStates;
	}
}
