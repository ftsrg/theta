package hu.bme.mit.inf.ttmc.analysis.pred.sts;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.analysis.ErrorStates;
import hu.bme.mit.inf.ttmc.analysis.pred.PredState;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.expr.impl.Exprs;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;
import hu.bme.mit.inf.ttmc.solver.Solver;

public class PredSTSErrorStates implements ErrorStates<PredState> {

	private final Solver solver;
	private final STS sts;
	private final Expr<? extends BoolType> negProp;

	public PredSTSErrorStates(final STS sts, final Solver solver) {
		this.solver = checkNotNull(solver);
		this.sts = checkNotNull(sts);
		this.negProp = Exprs.Not(sts.getProp());
	}

	@Override
	public boolean isError(final PredState state) {
		solver.push();
		solver.add(sts.unrollInv(0));
		solver.add(sts.unroll(state.asExpr(), 0));
		solver.add(sts.unroll(negProp, 0));
		solver.check();
		final boolean isError = solver.getStatus().boolValue();
		solver.pop();
		return isError;
	}

}
