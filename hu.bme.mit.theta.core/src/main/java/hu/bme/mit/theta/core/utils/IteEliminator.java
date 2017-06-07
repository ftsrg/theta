package hu.bme.mit.theta.core.utils;

import static hu.bme.mit.theta.core.type.anytype.Exprs.Ite;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Or;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.Type;
import hu.bme.mit.theta.core.type.anytype.IteExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

final class IteEliminator {

	private IteEliminator() {
	}

	public static <T extends Type> Expr<T> eliminateIte(final Expr<T> expr) {
		return removeIte(propagateIte(expr));
	}

	/*
	 * Helper methods
	 */

	private static <T extends Type> Expr<T> removeIte(final Expr<T> expr) {
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
			return expr.map(IteEliminator::removeIte);
		}
	}

	private static <T extends Type> Expr<T> propagateIte(final Expr<T> expr) {
		if (expr instanceof IteExpr) {
			final IteExpr<T> iteExpr = (IteExpr<T>) expr;
			// Apply propagation to operand(s)
			return iteExpr.withThen(propagateIte(iteExpr.getThen())).withElse(propagateIte(iteExpr.getElse()));
		} else {
			// Apply propagation to operand(s) first, then apply pushdown
			return pushIte(expr.map(IteEliminator::propagateIte));
		}
	}

	private static <T extends Type> Expr<T> pushIte(final Expr<T> expr) {
		if (expr instanceof IteExpr) {
			return expr;
		} else {
			return rewrite(expr, expr.getOps());
		}
	}

	// Push expression below ITE, e.g.:
	// X + ite(C,T,E) + Y => ite(C,X+T+Y,X+E+Y)
	private static <ExprType extends Type, OpType extends Type> Expr<ExprType> rewrite(final Expr<ExprType> expr,
			final List<? extends Expr<OpType>> ops) {

		// Get the first operand which is an ITE
		final Optional<? extends Expr<OpType>> optIte = ops.stream().filter(op -> op instanceof IteExpr).findFirst();

		// Nothing to do if the none of the operands are ITE
		if (!optIte.isPresent()) {
			return expr;
		}

		final IteExpr<OpType> ite = (IteExpr<OpType>) optIte.get();

		// Nothing to do if the operand is of bool type
		if (ite.getType() instanceof BoolType) {
			return expr;
		}

		final List<Expr<OpType>> thenOps = new ArrayList<>(ops.size());
		final List<Expr<OpType>> elseOps = new ArrayList<>(ops.size());

		for (final Expr<OpType> op : ops) {
			if (op == ite) {
				thenOps.add(ite.getThen());
				elseOps.add(ite.getElse());
			} else {
				thenOps.add(op);
				elseOps.add(op);
			}
		}

		return Ite(ite.getCond(), pushIte(expr.withOps(thenOps)), pushIte(expr.withOps(elseOps)));
	}

}
