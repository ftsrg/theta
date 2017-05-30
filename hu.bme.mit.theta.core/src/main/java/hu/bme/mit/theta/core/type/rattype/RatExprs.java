package hu.bme.mit.theta.core.type.rattype;

import java.util.Collection;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.RatType;

public final class RatExprs {

	private RatExprs() {
	}

	public static RatLitExpr Rat(final int num, final int denom) {
		return new RatLitExpr(num, denom);
	}

	public static RatAddExpr Add(final Collection<? extends Expr<? extends RatType>> ops) {
		return new RatAddExpr(ops);
	}

	public static RatSubExpr Sub(final Expr<? extends RatType> leftOp, final Expr<? extends RatType> rightOp) {
		return new RatSubExpr(leftOp, rightOp);
	}

	public static RatMulExpr Mul(final Collection<? extends Expr<? extends RatType>> ops) {
		return new RatMulExpr(ops);
	}

	public static RatDivExpr RatDiv(final Expr<? extends RatType> leftOp, final Expr<? extends RatType> rightOp) {
		return new RatDivExpr(leftOp, rightOp);
	}

	/*
	 * Convenience methods
	 */

	public static RatAddExpr Add(final Expr<? extends RatType> op1, final Expr<? extends RatType> op2) {
		return Add(ImmutableList.of(op1, op2));
	}

	public static RatAddExpr Add(final Expr<? extends RatType> op1, final Expr<? extends RatType> op2,
			final Expr<? extends RatType> op3) {
		return Add(ImmutableList.of(op1, op2, op3));
	}

	public static RatAddExpr Add(final Expr<? extends RatType> op1, final Expr<? extends RatType> op2,
			final Expr<? extends RatType> op3, final Expr<? extends RatType> op4) {
		return Add(ImmutableList.of(op1, op2, op3, op4));
	}

	public static RatAddExpr Add(final Expr<? extends RatType> op1, final Expr<? extends RatType> op2,
			final Expr<? extends RatType> op3, final Expr<? extends RatType> op4, final Expr<? extends RatType> op5) {
		return Add(ImmutableList.of(op1, op2, op3, op4, op5));
	}

	////

	public static RatMulExpr Mul(final Expr<? extends RatType> op1, final Expr<? extends RatType> op2) {
		return Mul(ImmutableList.of(op1, op2));
	}

	public static RatMulExpr Mul(final Expr<? extends RatType> op1, final Expr<? extends RatType> op2,
			final Expr<? extends RatType> op3) {
		return Mul(ImmutableList.of(op1, op2, op3));
	}

	public static RatMulExpr Mul(final Expr<? extends RatType> op1, final Expr<? extends RatType> op2,
			final Expr<? extends RatType> op3, final Expr<? extends RatType> op4) {
		return Mul(ImmutableList.of(op1, op2, op3, op4));
	}

	public static RatMulExpr Mul(final Expr<? extends RatType> op1, final Expr<? extends RatType> op2,
			final Expr<? extends RatType> op3, final Expr<? extends RatType> op4, final Expr<? extends RatType> op5) {
		return Mul(ImmutableList.of(op1, op2, op3, op4, op5));
	}

}
