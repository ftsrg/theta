package hu.bme.mit.theta.analysis.pred;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Collections;
import java.util.function.Function;

import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation;
import hu.bme.mit.theta.analysis.expr.refinement.RefutationToPrec;
import hu.bme.mit.theta.analysis.pred.ExprSplitters.ExprSplitter;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.utils.impl.ExprUtils;
import hu.bme.mit.theta.solver.Solver;

public class ItpRefToSimplePredPrec implements RefutationToPrec<SimplePredPrec, ItpRefutation> {

	private final Solver solver;
	private final ExprSplitter exprSplitter;

	public ItpRefToSimplePredPrec(final Solver solver, final ExprSplitter exprSplitter) {
		this.solver = checkNotNull(solver);
		this.exprSplitter = checkNotNull(exprSplitter);
	}

	@Override
	public SimplePredPrec toPrec(final ItpRefutation refutation, final int index) {
		final Expr<? extends BoolType> expr = refutation.get(index);
		final Collection<Expr<? extends BoolType>> exprs = exprSplitter.apply(expr);
		final SimplePredPrec prec = SimplePredPrec.create(exprs, solver);
		return prec;
	}

	@Override
	public SimplePredPrec join(final SimplePredPrec prec1, final SimplePredPrec prec2) {
		checkNotNull(prec1);
		checkNotNull(prec2);
		return prec1.join(prec2);
	}

	@Override
	public String toString() {
		return getClass().getSimpleName(); // TODO: splitting strategy should be included
	}

	public static Function<Expr<? extends BoolType>, Collection<Expr<? extends BoolType>>> whole() {
		return e -> Collections.singleton(e);
	}

	public static Function<Expr<? extends BoolType>, Collection<Expr<? extends BoolType>>> conjuncts() {
		return e -> ExprUtils.getConjuncts(e);
	}

	public static Function<Expr<? extends BoolType>, Collection<Expr<? extends BoolType>>> atoms() {
		return e -> ExprUtils.getAtoms(e);
	}

}
