package hu.bme.mit.theta.splittingcegar.common.utils;

import java.util.Collection;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.IteExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

/**
 * Collect condition formulas of ITE expressions.
 */
public final class IteCondCollector {

	private IteCondCollector() {
	}

	public static void collectIteConds(final Expr<?> expr, final Collection<Expr<BoolType>> collectTo) {
		if (expr instanceof IteExpr) {
			final IteExpr<?> iteExpr = (IteExpr<?>) expr;
			collectTo.add(iteExpr.getCond());
			collectIteConds(iteExpr.getThen(), collectTo);
			collectIteConds(iteExpr.getElse(), collectTo);
		} else {
			expr.getOps().forEach(op -> collectIteConds(op, collectTo));
		}
	}

}
