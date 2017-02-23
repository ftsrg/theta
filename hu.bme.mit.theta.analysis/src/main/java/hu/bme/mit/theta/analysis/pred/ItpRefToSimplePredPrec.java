package hu.bme.mit.theta.analysis.pred;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.expr.ItpRefutation;
import hu.bme.mit.theta.analysis.expr.RefutationToPrec;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.solver.Solver;

public class ItpRefToSimplePredPrec implements RefutationToPrec<SimplePredPrec, ItpRefutation> {

	private final Solver solver;

	public ItpRefToSimplePredPrec(final Solver solver) {
		this.solver = checkNotNull(solver);
	}

	@Override
	public SimplePredPrec toPrec(final ItpRefutation refutation, final int index) {
		final Expr<? extends BoolType> expr = refutation.get(index);
		final SimplePredPrec prec = SimplePredPrec.create(expr, solver);
		return prec;
	}

	@Override
	public SimplePredPrec join(final SimplePredPrec prec1, final SimplePredPrec prec2) {
		checkNotNull(prec1);
		checkNotNull(prec2);
		return prec1.join(prec2);
	}

}
