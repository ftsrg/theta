package hu.bme.mit.inf.ttmc.analysis.sts.expl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.analysis.TargetPredicate;
import hu.bme.mit.inf.ttmc.analysis.expl.ExplState;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.expr.impl.Exprs;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.utils.PathUtils;
import hu.bme.mit.inf.ttmc.formalism.utils.impl.FormalismUtils;
import hu.bme.mit.inf.ttmc.solver.Solver;

public class STSExplTargetPredicate implements TargetPredicate<ExplState, Expr<? extends BoolType>> {

	private final Solver solver;

	public STSExplTargetPredicate(final Solver solver) {
		this.solver = checkNotNull(solver);
	}

	@Override
	public boolean isTargetState(final ExplState state, final Expr<? extends BoolType> target) {
		checkNotNull(state);
		checkNotNull(target);

		final Expr<? extends BoolType> simplified = FormalismUtils.simplify(target, state);
		if (simplified.equals(Exprs.True()) || simplified.equals(Exprs.False())) {
			return simplified.equals(Exprs.True());
		} else {
			solver.push();
			solver.add(PathUtils.unfold(simplified, 0));
			solver.check();
			final boolean result = solver.getStatus().boolValue();
			solver.pop();
			return result;
		}

	}

}