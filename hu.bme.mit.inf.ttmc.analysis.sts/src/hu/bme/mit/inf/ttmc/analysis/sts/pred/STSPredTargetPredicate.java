package hu.bme.mit.inf.ttmc.analysis.sts.pred;

import hu.bme.mit.inf.ttmc.analysis.TargetPredicate;
import hu.bme.mit.inf.ttmc.analysis.pred.PredState;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.utils.PathUtils;
import hu.bme.mit.inf.ttmc.solver.Solver;

public class STSPredTargetPredicate implements TargetPredicate<PredState, Expr<? extends BoolType>> {

	private final Solver solver;

	STSPredTargetPredicate(final Solver solver) {
		this.solver = solver;
	}

	@Override
	public boolean isTargetState(final PredState state, final Expr<? extends BoolType> target) {
		solver.push();
		solver.add(PathUtils.unfold(state.toExpr(), 0));
		solver.add(PathUtils.unfold(target, 0));
		solver.check();
		final boolean isError = solver.getStatus().boolValue();
		solver.pop();
		return isError;
	}

}
