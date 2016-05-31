package hu.bme.mit.inf.ttmc.analysis.expl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.analysis.StatePredicate;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.expr.impl.Exprs;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.utils.PathUtils;
import hu.bme.mit.inf.ttmc.formalism.utils.impl.FormalismUtils;
import hu.bme.mit.inf.ttmc.solver.Solver;
import hu.bme.mit.inf.ttmc.solver.SolverManager;

public class ExplStatePredicate implements StatePredicate<ExplState> {

	private final Solver solver;
	private final Expr<? extends BoolType> property;

	public ExplStatePredicate(final SolverManager manager, final Expr<? extends BoolType> property) {
		checkNotNull(manager);
		checkNotNull(property);
		solver = manager.createSolver(true, true);
		this.property = property;
	}

	@Override
	public boolean test(final ExplState state) {
		final Expr<? extends BoolType> simplified = FormalismUtils.simplify(property, state);
		if (simplified.equals(Exprs.True()) || simplified.equals(Exprs.False())) {
			return simplified.equals(Exprs.True());
		} else {
			solver.push();
			solver.add(PathUtils.unfold(simplified, 0));
			solver.check();
			final boolean target = solver.getStatus().boolValue();
			solver.pop();
			return target;
		}
	}

}
