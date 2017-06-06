package hu.bme.mit.theta.core.utils;

import static hu.bme.mit.theta.core.utils.ItePusher.pushIte;

import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.Type;
import hu.bme.mit.theta.core.type.anytype.IteExpr;

public final class ItePropagator {

	private ItePropagator() {
	}

	public static <T extends Type> Expr<T> propagateIte(final Expr<T> expr) {
		if (expr instanceof IteExpr) {
			final IteExpr<T> iteExpr = (IteExpr<T>) expr;
			// Apply propagation to operand(s)
			return iteExpr.withThen(propagateIte(iteExpr.getThen())).withElse(propagateIte(iteExpr.getElse()));
		} else {
			// Apply propagation to operand(s) first, then apply pushdown
			return pushIte(expr.rewrite(ItePropagator::propagateIte));
		}
	}

}
