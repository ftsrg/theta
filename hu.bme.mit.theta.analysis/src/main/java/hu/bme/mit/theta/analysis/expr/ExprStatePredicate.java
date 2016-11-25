package hu.bme.mit.theta.analysis.expr;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.function.Predicate;

import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.utils.impl.PathUtils;
import hu.bme.mit.theta.solver.Solver;

public class ExprStatePredicate implements Predicate<ExprState> {

	private final Expr<? extends BoolType> expr;
	private Expr<? extends BoolType> expr0;
	private final Solver solver;

	public ExprStatePredicate(final Expr<? extends BoolType> expr, final Solver solver) {
		this.expr = checkNotNull(expr);
		this.solver = checkNotNull(solver);
		this.expr0 = null;
	}

	@Override
	public boolean test(final ExprState state) {
		if (expr0 == null) {
			expr0 = PathUtils.unfold(expr, 0);
		}
		solver.push();
		solver.add(PathUtils.unfold(state.toExpr(), 0));
		solver.add(expr0);
		final boolean result = solver.check().isSat();
		solver.pop();
		return result;
	}

	public Expr<? extends BoolType> toExpr() {
		return expr;
	}

	@Override
	public String toString() {
		return ObjectUtils.toStringBuilder(getClass().getSimpleName()).add(expr).toString();
	}
}
