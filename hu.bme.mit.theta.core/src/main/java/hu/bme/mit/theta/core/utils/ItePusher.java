package hu.bme.mit.theta.core.utils;

import static hu.bme.mit.theta.core.type.anytype.Exprs.Ite;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.anytype.IteExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

public final class ItePusher {

	private ItePusher() {
	}

	public static <T extends Type> Expr<T> pushIte(final Expr<T> expr) {
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
