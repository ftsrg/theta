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

	public static RatAddExpr Add(final Collection<? extends Expr<RatType>> ops) {
		return new RatAddExpr(ops);
	}

	public static RatSubExpr Sub(final Expr<RatType> leftOp, final Expr<RatType> rightOp) {
		return new RatSubExpr(leftOp, rightOp);
	}

	public static RatNegExpr Neg(final Expr<RatType> op) {
		return new RatNegExpr(op);
	}

	public static RatMulExpr Mul(final Collection<? extends Expr<RatType>> ops) {
		return new RatMulExpr(ops);
	}

	public static RatDivExpr Div(final Expr<RatType> leftOp, final Expr<RatType> rightOp) {
		return new RatDivExpr(leftOp, rightOp);
	}

	public static RatEqExpr Eq(final Expr<RatType> leftOp, final Expr<RatType> rightOp) {
		return new RatEqExpr(leftOp, rightOp);
	}

	public static RatNeqExpr Neq(final Expr<RatType> leftOp, final Expr<RatType> rightOp) {
		return new RatNeqExpr(leftOp, rightOp);
	}

	public static RatLtExpr Lt(final Expr<RatType> leftOp, final Expr<RatType> rightOp) {
		return new RatLtExpr(leftOp, rightOp);
	}

	public static RatLeqExpr Leq(final Expr<RatType> leftOp, final Expr<RatType> rightOp) {
		return new RatLeqExpr(leftOp, rightOp);
	}

	public static RatGtExpr Gt(final Expr<RatType> leftOp, final Expr<RatType> rightOp) {
		return new RatGtExpr(leftOp, rightOp);
	}

	public static RatGeqExpr Geq(final Expr<RatType> leftOp, final Expr<RatType> rightOp) {
		return new RatGeqExpr(leftOp, rightOp);
	}

	/*
	 * Convenience methods
	 */

	public static RatAddExpr Add(final Expr<RatType> op1, final Expr<RatType> op2) {
		return Add(ImmutableList.of(op1, op2));
	}

	public static RatAddExpr Add(final Expr<RatType> op1, final Expr<RatType> op2, final Expr<RatType> op3) {
		return Add(ImmutableList.of(op1, op2, op3));
	}

	public static RatAddExpr Add(final Expr<RatType> op1, final Expr<RatType> op2, final Expr<RatType> op3,
			final Expr<RatType> op4) {
		return Add(ImmutableList.of(op1, op2, op3, op4));
	}

	public static RatAddExpr Add(final Expr<RatType> op1, final Expr<RatType> op2, final Expr<RatType> op3,
			final Expr<RatType> op4, final Expr<RatType> op5) {
		return Add(ImmutableList.of(op1, op2, op3, op4, op5));
	}

	////

	public static RatMulExpr Mul(final Expr<RatType> op1, final Expr<RatType> op2) {
		return Mul(ImmutableList.of(op1, op2));
	}

	public static RatMulExpr Mul(final Expr<RatType> op1, final Expr<RatType> op2, final Expr<RatType> op3) {
		return Mul(ImmutableList.of(op1, op2, op3));
	}

	public static RatMulExpr Mul(final Expr<RatType> op1, final Expr<RatType> op2, final Expr<RatType> op3,
			final Expr<RatType> op4) {
		return Mul(ImmutableList.of(op1, op2, op3, op4));
	}

	public static RatMulExpr Mul(final Expr<RatType> op1, final Expr<RatType> op2, final Expr<RatType> op3,
			final Expr<RatType> op4, final Expr<RatType> op5) {
		return Mul(ImmutableList.of(op1, op2, op3, op4, op5));
	}

}
