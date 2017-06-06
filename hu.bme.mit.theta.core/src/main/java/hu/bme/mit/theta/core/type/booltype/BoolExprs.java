package hu.bme.mit.theta.core.type.booltype;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.decl.ParamDecl;

public final class BoolExprs {

	private BoolExprs() {
	}

	public static BoolType Bool() {
		return BoolType.getInstance();
	}

	public static BoolLitExpr Bool(final boolean value) {
		if (value) {
			return True();
		} else {
			return False();
		}
	}

	public static TrueExpr True() {
		return TrueExpr.getInstance();
	}

	public static FalseExpr False() {
		return FalseExpr.getInstance();
	}

	public static NotExpr Not(final Expr<BoolType> op) {
		return new NotExpr(op);
	}

	public static ImplyExpr Imply(final Expr<BoolType> leftOp, final Expr<BoolType> rightOp) {
		return new ImplyExpr(leftOp, rightOp);
	}

	public static IffExpr Iff(final Expr<BoolType> leftOp, final Expr<BoolType> rightOp) {
		return new IffExpr(leftOp, rightOp);
	}

	public static AndExpr And(final Iterable<? extends Expr<BoolType>> ops) {
		return new AndExpr(ops);
	}

	public static OrExpr Or(final Iterable<? extends Expr<BoolType>> ops) {
		return new OrExpr(ops);
	}

	public static ForallExpr Forall(final Iterable<? extends ParamDecl<?>> paramDecls, final Expr<BoolType> op) {
		return new ForallExpr(paramDecls, op);
	}

	public static ExistsExpr Exists(final Iterable<? extends ParamDecl<?>> paramDecls, final Expr<BoolType> op) {
		return new ExistsExpr(paramDecls, op);
	}

	/*
	 * Convenience methods
	 */

	public static AndExpr And(final Expr<BoolType> op1, final Expr<BoolType> op2) {
		return And(ImmutableList.of(op1, op2));
	}

	public static AndExpr And(final Expr<BoolType> op1, final Expr<BoolType> op2, final Expr<BoolType> op3) {
		return And(ImmutableList.of(op1, op2, op3));
	}

	public static AndExpr And(final Expr<BoolType> op1, final Expr<BoolType> op2, final Expr<BoolType> op3,
			final Expr<BoolType> op4) {
		return And(ImmutableList.of(op1, op2, op3, op4));
	}

	public static AndExpr And(final Expr<BoolType> op1, final Expr<BoolType> op2, final Expr<BoolType> op3,
			final Expr<BoolType> op4, final Expr<BoolType> op5) {
		return And(ImmutableList.of(op1, op2, op3, op4, op5));
	}

	////

	public static OrExpr Or(final Expr<BoolType> op1, final Expr<BoolType> op2) {
		return Or(ImmutableList.of(op1, op2));
	}

	public static OrExpr Or(final Expr<BoolType> op1, final Expr<BoolType> op2, final Expr<BoolType> op3) {
		return Or(ImmutableList.of(op1, op2, op3));
	}

	public static OrExpr Or(final Expr<BoolType> op1, final Expr<BoolType> op2, final Expr<BoolType> op3,
			final Expr<BoolType> op4) {
		return Or(ImmutableList.of(op1, op2, op3, op4));
	}

	public static OrExpr Or(final Expr<BoolType> op1, final Expr<BoolType> op2, final Expr<BoolType> op3,
			final Expr<BoolType> op4, final Expr<BoolType> op5) {
		return Or(ImmutableList.of(op1, op2, op3, op4, op5));
	}

}
