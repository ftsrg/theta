package hu.bme.mit.theta.core.type.inttype;

import java.util.Collection;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.IntType;

public final class IntExprs {

	private IntExprs() {
	}

	public static IntLitExpr Int(final int value) {
		return new IntLitExpr(value);
	}

	public static IntToRatExpr ToRat(final Expr<IntType> op) {
		return new IntToRatExpr(op);
	}

	public static IntAddExpr Add(final Collection<? extends Expr<IntType>> ops) {
		return new IntAddExpr(ops);
	}

	public static IntSubExpr Sub(final Expr<IntType> leftOp, final Expr<IntType> rightOp) {
		return new IntSubExpr(leftOp, rightOp);
	}

	public static IntMulExpr Mul(final Collection<? extends Expr<IntType>> ops) {
		return new IntMulExpr(ops);
	}

	public static IntDivExpr Div(final Expr<IntType> leftOp, final Expr<IntType> rightOp) {
		return new IntDivExpr(leftOp, rightOp);
	}

	public static ModExpr Mod(final Expr<IntType> leftOp, final Expr<IntType> rightOp) {
		return new ModExpr(leftOp, rightOp);
	}

	public static RemExpr Rem(final Expr<IntType> leftOp, final Expr<IntType> rightOp) {
		return new RemExpr(leftOp, rightOp);
	}

	/*
	 * Convenience methods
	 */

	public static IntAddExpr Add(final Expr<IntType> op1, final Expr<IntType> op2) {
		return Add(ImmutableList.of(op1, op2));
	}

	public static IntAddExpr Add(final Expr<IntType> op1, final Expr<IntType> op2, final Expr<IntType> op3) {
		return Add(ImmutableList.of(op1, op2, op3));
	}

	public static IntAddExpr Add(final Expr<IntType> op1, final Expr<IntType> op2, final Expr<IntType> op3,
			final Expr<IntType> op4) {
		return Add(ImmutableList.of(op1, op2, op3, op4));
	}

	public static IntAddExpr Add(final Expr<IntType> op1, final Expr<IntType> op2, final Expr<IntType> op3,
			final Expr<IntType> op4, final Expr<IntType> op5) {
		return Add(ImmutableList.of(op1, op2, op3, op4, op5));
	}

	////

	public static IntMulExpr Mul(final Expr<IntType> op1, final Expr<IntType> op2) {
		return Mul(ImmutableList.of(op1, op2));
	}

	public static IntMulExpr Mul(final Expr<IntType> op1, final Expr<IntType> op2, final Expr<IntType> op3) {
		return Mul(ImmutableList.of(op1, op2, op3));
	}

	public static IntMulExpr Mul(final Expr<IntType> op1, final Expr<IntType> op2, final Expr<IntType> op3,
			final Expr<IntType> op4) {
		return Mul(ImmutableList.of(op1, op2, op3, op4));
	}

	public static IntMulExpr Mul(final Expr<IntType> op1, final Expr<IntType> op2, final Expr<IntType> op3,
			final Expr<IntType> op4, final Expr<IntType> op5) {
		return Mul(ImmutableList.of(op1, op2, op3, op4, op5));
	}

}
