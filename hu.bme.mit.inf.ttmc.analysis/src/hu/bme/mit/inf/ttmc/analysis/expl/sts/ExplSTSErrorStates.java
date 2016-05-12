package hu.bme.mit.inf.ttmc.analysis.expl.sts;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.analysis.ErrorStates;
import hu.bme.mit.inf.ttmc.analysis.expl.ExplState;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.expr.impl.Exprs;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;
import hu.bme.mit.inf.ttmc.formalism.utils.impl.FormalismUtils;
import hu.bme.mit.inf.ttmc.solver.Solver;

public class ExplSTSErrorStates implements ErrorStates<ExplState> {

	private final Solver solver;
	private final STS sts;
	private final Expr<? extends BoolType> negProp;

	public ExplSTSErrorStates(final STS sts, final Solver solver) {
		this.solver = checkNotNull(solver);
		this.sts = checkNotNull(sts);
		this.negProp = Exprs.Not(sts.getProp());
	}

	@Override
	public boolean isError(final ExplState state) {
		final Expr<? extends BoolType> simplified = FormalismUtils.simplify(negProp, state);
		if (simplified.equals(Exprs.True()) || simplified.equals(Exprs.False())) {
			return simplified.equals(Exprs.True());
		} else {
			solver.push();
			solver.add(sts.unrollInv(0));
			solver.add(sts.unroll(simplified, 0));
			solver.check();
			final boolean isError = solver.getStatus().boolValue();
			solver.pop();
			return isError;
		}
	}

}
