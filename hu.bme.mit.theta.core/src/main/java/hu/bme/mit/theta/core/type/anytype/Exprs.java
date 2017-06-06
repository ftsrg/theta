package hu.bme.mit.theta.core.type.anytype;

import static com.google.common.base.Preconditions.checkArgument;

import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolType;

public final class Exprs {

	private Exprs() {
	}

	public static <DeclType extends Type> RefExpr<DeclType> Ref(final Decl<DeclType> decl) {
		return new RefExpr<>(decl);
	}

	public static <ExprType extends Type> IteExpr<ExprType> Ite(final Expr<BoolType> cond, final Expr<ExprType> then, final Expr<ExprType> elze) {
		return new IteExpr<>(cond, then, elze);
	}

	public static <ExprType extends Type> PrimeExpr<ExprType> Prime(final Expr<ExprType> op) {
		return new PrimeExpr<>(op);
	}

	/*
	 * Convenience methods
	 */

	public static <ExprType extends Type> PrimeExpr<ExprType> Prime(final Expr<ExprType> op, final int i) {
		checkArgument(i > 0);
		if (i == 1) {
			return Prime(op);
		} else {
			return Prime(Prime(op, i - 1));
		}
	}

}
