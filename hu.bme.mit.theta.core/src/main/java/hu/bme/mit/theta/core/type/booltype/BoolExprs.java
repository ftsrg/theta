package hu.bme.mit.theta.core.type.booltype;

import java.util.Collection;
import java.util.List;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.expr.Expr;

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

	public static NotExpr Not(final Expr<? extends BoolType> op) {
		return new NotExpr(op);
	}

	public static ImplyExpr Imply(final Expr<? extends BoolType> leftOp, final Expr<? extends BoolType> rightOp) {
		return new ImplyExpr(leftOp, rightOp);
	}

	public static IffExpr Iff(final Expr<? extends BoolType> leftOp, final Expr<? extends BoolType> rightOp) {
		return new IffExpr(leftOp, rightOp);
	}

	public static AndExpr And(final Collection<? extends Expr<? extends BoolType>> ops) {
		return new AndExpr(ops);
	}

	public static OrExpr Or(final Collection<? extends Expr<? extends BoolType>> ops) {
		return new OrExpr(ops);
	}

	public static ForallExpr Forall(final List<? extends ParamDecl<?>> paramDecls, final Expr<? extends BoolType> op) {
		return new ForallExpr(paramDecls, op);
	}

	public static ExistsExpr Exists(final List<? extends ParamDecl<?>> paramDecls, final Expr<? extends BoolType> op) {
		return new ExistsExpr(paramDecls, op);
	}

	/*
	 * Convenience methods
	 */

	public static AndExpr And(final Expr<? extends BoolType> op1, final Expr<? extends BoolType> op2) {
		return And(ImmutableList.of(op1, op2));
	}

	public static AndExpr And(final Expr<? extends BoolType> op1, final Expr<? extends BoolType> op2,
			final Expr<? extends BoolType> op3) {
		return And(ImmutableList.of(op1, op2, op3));
	}

	public static AndExpr And(final Expr<? extends BoolType> op1, final Expr<? extends BoolType> op2,
			final Expr<? extends BoolType> op3, final Expr<? extends BoolType> op4) {
		return And(ImmutableList.of(op1, op2, op3, op4));
	}

	public static AndExpr And(final Expr<? extends BoolType> op1, final Expr<? extends BoolType> op2,
			final Expr<? extends BoolType> op3, final Expr<? extends BoolType> op4,
			final Expr<? extends BoolType> op5) {
		return And(ImmutableList.of(op1, op2, op3, op4, op5));
	}

	////

	public static OrExpr Or(final Expr<? extends BoolType> op1, final Expr<? extends BoolType> op2) {
		return Or(ImmutableList.of(op1, op2));
	}

	public static OrExpr Or(final Expr<? extends BoolType> op1, final Expr<? extends BoolType> op2,
			final Expr<? extends BoolType> op3) {
		return Or(ImmutableList.of(op1, op2, op3));
	}

	public static OrExpr Or(final Expr<? extends BoolType> op1, final Expr<? extends BoolType> op2,
			final Expr<? extends BoolType> op3, final Expr<? extends BoolType> op4) {
		return Or(ImmutableList.of(op1, op2, op3, op4));
	}

	public static OrExpr Or(final Expr<? extends BoolType> op1, final Expr<? extends BoolType> op2,
			final Expr<? extends BoolType> op3, final Expr<? extends BoolType> op4,
			final Expr<? extends BoolType> op5) {
		return Or(ImmutableList.of(op1, op2, op3, op4, op5));
	}

}
