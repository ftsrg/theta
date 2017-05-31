package hu.bme.mit.theta.core.expr;

import static com.google.common.base.Preconditions.checkArgument;

import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.RatType;
import hu.bme.mit.theta.core.type.Type;

public final class Exprs {

	private Exprs() {
	}

	public static <DeclType extends Type> RefExpr<DeclType> Ref(final Decl<DeclType> decl) {
		return new RefExpr<>(decl);
	}

	public static <T extends Type> PrimedExpr<T> Prime(final Expr<? extends T> op) {
		return new PrimedExpr<>(op);
	}

	public static EqExpr Eq(final Expr<? extends Type> leftOp, final Expr<? extends Type> rightOp) {
		return new EqExpr(leftOp, rightOp);
	}

	public static NeqExpr Neq(final Expr<? extends Type> leftOp, final Expr<? extends Type> rightOp) {
		return new NeqExpr(leftOp, rightOp);
	}

	public static LtExpr Lt(final Expr<? extends RatType> leftOp, final Expr<? extends RatType> rightOp) {
		return new LtExpr(leftOp, rightOp);
	}

	public static LeqExpr Leq(final Expr<? extends RatType> leftOp, final Expr<? extends RatType> rightOp) {
		return new LeqExpr(leftOp, rightOp);
	}

	public static GtExpr Gt(final Expr<? extends RatType> leftOp, final Expr<? extends RatType> rightOp) {
		return new GtExpr(leftOp, rightOp);
	}

	public static GeqExpr Geq(final Expr<? extends RatType> leftOp, final Expr<? extends RatType> rightOp) {
		return new GeqExpr(leftOp, rightOp);
	}

	public static <T extends Type> IteExpr<T> Ite(final Expr<? extends BoolType> cond, final Expr<? extends T> then,
			final Expr<? extends T> elze) {
		return new IteExpr<>(cond, then, elze);
	}

	/*
	 * Convenience methods
	 */

	public static <T extends Type> PrimedExpr<T> Prime(final Expr<? extends T> op, final int i) {
		checkArgument(i > 0);
		if (i == 1) {
			return new PrimedExpr<>(op);
		} else {
			return new PrimedExpr<>(Prime(op, i - 1));
		}
	}

}
