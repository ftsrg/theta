package hu.bme.mit.inf.ttmc.analysis.pred;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.analysis.Domain;
import hu.bme.mit.inf.ttmc.core.expr.impl.Exprs;
import hu.bme.mit.inf.ttmc.solver.Solver;

public class PredDomain implements Domain<PredState> {

	private final Solver solver;

	public PredDomain(final Solver solver) {
		this.solver = checkNotNull(solver);
	}

	@Override
	public PredState join(final PredState state1, final PredState state2) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public boolean isLeq(final PredState state1, final PredState state2) {
		solver.push();
		solver.add(state1.getPreds());
		solver.add(Exprs.Not(Exprs.And(state2.getPreds())));
		final boolean result = !solver.check().boolValue();
		solver.pop();
		return result;
	}

}
