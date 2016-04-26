package hu.bme.mit.inf.ttmc.analysis.pred;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.analysis.Domain;
import hu.bme.mit.inf.ttmc.core.expr.impl.Exprs;
import hu.bme.mit.inf.ttmc.formalism.utils.ExprUnroller;
import hu.bme.mit.inf.ttmc.solver.Solver;

public class PredDomain implements Domain<PredState> {

	private final Solver solver;
	private final ExprUnroller unroller;

	public PredDomain(final Solver solver, final ExprUnroller unroller) {
		this.solver = checkNotNull(solver);
		this.unroller = checkNotNull(unroller);
	}

	@Override
	public PredState join(final PredState state1, final PredState state2) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public boolean isLeq(final PredState state1, final PredState state2) {
		solver.push();
		solver.add(unroller.unroll(state1.getPreds(), 0));
		solver.add(Exprs.Not(Exprs.And(unroller.unroll(state2.getPreds(), 0))));
		final boolean isLeq = !solver.check().boolValue();
		solver.pop();
		return isLeq;
	}

}
