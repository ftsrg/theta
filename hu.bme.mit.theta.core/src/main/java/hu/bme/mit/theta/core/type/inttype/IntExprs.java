package hu.bme.mit.theta.core.type.inttype;

import java.util.Collection;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.core.Expr;

public final class IntExprs {

	private IntExprs() {
	}

	public static IntType Int() {
		return IntType.getInstance();
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

	public static IntNegExpr Neg(final Expr<IntType> op) {
		return new IntNegExpr(op);
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

	public static IntEqExpr Eq(final Expr<IntType> leftOp, final Expr<IntType> rightOp) {
		return new IntEqExpr(leftOp, rightOp);
	}

	public static IntNeqExpr Neq(final Expr<IntType> leftOp, final Expr<IntType> rightOp) {
		return new IntNeqExpr(leftOp, rightOp);
	}

	public static IntLtExpr Lt(final Expr<IntType> leftOp, final Expr<IntType> rightOp) {
		return new IntLtExpr(leftOp, rightOp);
	}

	public static IntLeqExpr Leq(final Expr<IntType> leftOp, final Expr<IntType> rightOp) {
		return new IntLeqExpr(leftOp, rightOp);
	}

	public static IntGtExpr Gt(final Expr<IntType> leftOp, final Expr<IntType> rightOp) {
		return new IntGtExpr(leftOp, rightOp);
	}

	public static IntGeqExpr Geq(final Expr<IntType> leftOp, final Expr<IntType> rightOp) {
		return new IntGeqExpr(leftOp, rightOp);
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
