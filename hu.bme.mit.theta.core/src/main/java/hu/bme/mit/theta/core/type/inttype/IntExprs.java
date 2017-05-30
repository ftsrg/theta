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

	public static IntToRatExpr ToRat(final Expr<? extends IntType> op) {
		return new IntToRatExpr(op);
	}

	public static IntAddExpr Add(final Collection<? extends Expr<? extends IntType>> ops) {
		return new IntAddExpr(ops);
	}

	public static IntSubExpr Sub(final Expr<? extends IntType> leftOp, final Expr<? extends IntType> rightOp) {
		return new IntSubExpr(leftOp, rightOp);
	}

	public static IntMulExpr Mul(final Collection<? extends Expr<? extends IntType>> ops) {
		return new IntMulExpr(ops);
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

	/*
	 * Convenience methods
	 */

	public static IntAddExpr Add(final Expr<? extends IntType> op1, final Expr<? extends IntType> op2) {
		return Add(ImmutableList.of(op1, op2));
	}

	public static IntAddExpr Add(final Expr<? extends IntType> op1, final Expr<? extends IntType> op2,
			final Expr<? extends IntType> op3) {
		return Add(ImmutableList.of(op1, op2, op3));
	}

	public static IntAddExpr Add(final Expr<? extends IntType> op1, final Expr<? extends IntType> op2,
			final Expr<? extends IntType> op3, final Expr<? extends IntType> op4) {
		return Add(ImmutableList.of(op1, op2, op3, op4));
	}

	public static IntAddExpr Add(final Expr<? extends IntType> op1, final Expr<? extends IntType> op2,
			final Expr<? extends IntType> op3, final Expr<? extends IntType> op4, final Expr<? extends IntType> op5) {
		return Add(ImmutableList.of(op1, op2, op3, op4, op5));
	}

	////

	public static IntMulExpr Mul(final Expr<? extends IntType> op1, final Expr<? extends IntType> op2) {
		return Mul(ImmutableList.of(op1, op2));
	}

	public static IntMulExpr Mul(final Expr<? extends IntType> op1, final Expr<? extends IntType> op2,
			final Expr<? extends IntType> op3) {
		return Mul(ImmutableList.of(op1, op2, op3));
	}

	public static IntMulExpr Mul(final Expr<? extends IntType> op1, final Expr<? extends IntType> op2,
			final Expr<? extends IntType> op3, final Expr<? extends IntType> op4) {
		return Mul(ImmutableList.of(op1, op2, op3, op4));
	}

	public static IntMulExpr Mul(final Expr<? extends IntType> op1, final Expr<? extends IntType> op2,
			final Expr<? extends IntType> op3, final Expr<? extends IntType> op4, final Expr<? extends IntType> op5) {
		return Mul(ImmutableList.of(op1, op2, op3, op4, op5));
	}

}
