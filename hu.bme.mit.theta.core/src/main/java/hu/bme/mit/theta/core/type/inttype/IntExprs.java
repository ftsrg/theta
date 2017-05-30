package hu.bme.mit.theta.core.type.inttype;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.IntType;

public final class IntExprs {

	private IntExprs() {
	}

	public static IntLitExpr Int(final int value) {
		return new IntLitExpr(value);
	}

	public static IntToRatExpr ToRat(final Expr<? extends IntType> op) {
		return new IntToRatExpr(op);
	}

	public static IntDivExpr Div(final Expr<? extends IntType> leftOp, final Expr<? extends IntType> rightOp) {
		return new IntDivExpr(leftOp, rightOp);
	}

	public static ModExpr Mod(final Expr<? extends IntType> leftOp, final Expr<? extends IntType> rightOp) {
		return new ModExpr(leftOp, rightOp);
	}

	public static RemExpr Rem(final Expr<? extends IntType> leftOp, final Expr<? extends IntType> rightOp) {
		return new RemExpr(leftOp, rightOp);
	}

}
