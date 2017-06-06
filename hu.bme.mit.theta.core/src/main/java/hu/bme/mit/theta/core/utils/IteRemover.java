package hu.bme.mit.theta.core.utils;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Or;

import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.Type;
import hu.bme.mit.theta.core.type.anytype.IteExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

public final class IteRemover {

	private IteRemover() {
	}

	public static <T extends Type> Expr<T> removeIte(final Expr<T> expr) {
		if (expr instanceof IteExpr) {
			final IteExpr<T> iteExpr = (IteExpr<T>) expr;
			if (iteExpr.getType() instanceof BoolType) {
				final Expr<BoolType> cond = removeIte(iteExpr.getCond());
				final Expr<BoolType> then = TypeUtils.cast(removeIte(iteExpr.getThen()), Bool());
				final Expr<BoolType> elze = TypeUtils.cast(removeIte(iteExpr.getElse()), Bool());
				@SuppressWarnings("unchecked")
				final Expr<T> result = (Expr<T>) And(Or(Not(cond), then), Or(cond, elze));
				return result;
			} else {
				return expr;
			}
		} else {
			return expr.rewrite(IteRemover::removeIte);
		}
	}

}
